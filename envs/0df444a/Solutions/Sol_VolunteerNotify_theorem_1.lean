-- Prove2me | solution 1 for VolunteerNotify.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:22:09.496721+00:00
-- url     : https://prove2.me/submissions/acdcf989-74ff-4c99-ad35-23823a2e2716

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte
import Definitions.Def_VolunteerNotify_IsDP
import Definitions.Def_VolunteerNotify_Process
import Theorems.Thm_VolunteerNotify_proposition_2
import Theorems.Thm_VolunteerNotify_closing_step

open MeasureTheory

namespace VNAux

open VolunteerNotify

variable {V S T : ℕ}

lemma cdf_nonneg (I : Instance V S T) (n : ℕ) : 0 ≤ cdf I.g n :=
  Finset.sum_nonneg fun k _ => I.g_nonneg k

lemma cdf_le_one (I : Instance V S T) (n : ℕ) : cdf I.g n ≤ 1 :=
  sum_le_hasSum _ (fun i _ => I.g_nonneg i) I.g_hasSum

lemma cdf_zero (I : Instance V S T) : cdf I.g 0 = 0 := by
  simp [cdf, I.g_zero]

lemma cdf_succ (g : ℕ → ℝ) (n : ℕ) : cdf g (n + 1) = cdf g n + g (n + 1) := by
  unfold cdf
  rw [Finset.sum_range_succ]

lemma hazard_nonneg (I : Instance V S T) (k : ℕ) : 0 ≤ hazard I.g k := by
  unfold hazard
  split_ifs
  · norm_num
  · exact div_nonneg (I.g_nonneg k) (sub_nonneg.2 (cdf_le_one I _))

lemma hazard_bdd (I : Instance V S T) : BddBelow (Set.range fun τ : ℕ => hazard I.g (τ + 1)) :=
  ⟨0, by rintro _ ⟨τ, rfl⟩; exact hazard_nonneg I _⟩

lemma mdhr_nonneg (I : Instance V S T) : 0 ≤ mdhr I.g :=
  le_ciInf fun _ => hazard_nonneg I _

lemma mdhr_le_hazard (I : Instance V S T) (k : ℕ) : mdhr I.g ≤ hazard I.g (k + 1) :=
  ciInf_le (hazard_bdd I) k

lemma mdhr_le_one (I : Instance V S T) : mdhr I.g ≤ 1 := by
  refine (mdhr_le_hazard I 0).trans ?_
  have h1 : I.g 1 ≤ 1 := le_hasSum I.g_hasSum 1 fun j _ => I.g_nonneg j
  simp [hazard, cdf_zero, h1]

/-- (14)–(15): `1 − G(k + 1) ≤ (1 − q)(1 − G(k))`. -/
lemma tail_step (I : Instance V S T) (k : ℕ) :
    1 - cdf I.g (k + 1) ≤ (1 - mdhr I.g) * (1 - cdf I.g k) := by
  rw [cdf_succ]
  have hD : 0 ≤ 1 - cdf I.g k := sub_nonneg.2 (cdf_le_one I k)
  have hg := I.g_nonneg (k + 1)
  rcases hD.lt_or_eq with hpos | hzero
  · have hq := mdhr_le_hazard I k
    have hh : hazard I.g (k + 1) = I.g (k + 1) / (1 - cdf I.g k) := by
      simp [hazard, hpos.ne']
    rw [hh, le_div_iff₀ hpos] at hq
    nlinarith
  · rw [← hzero]
    nlinarith

/-- The load `∑_{u < t} c_u (1 − G(t − u))` of the earlier notifications at `t`, where
`c_u = ∑_s λ_{s,u} x_{v,s,u}`. -/
noncomputable def slack (I : Instance V S T) (x : Decision V S T) (v : Fin V) (t : Fin T) : ℝ :=
  ∑ u ∈ Finset.Iio t, (∑ s, I.lam s u * x v s u) * (1 - cdf I.g ((t : ℕ) - (u : ℕ)))

lemma c_nonneg (I : Instance V S T) (x : Decision V S T) (hx : x ∈ feasibleSet I) (v : Fin V)
    (u : Fin T) : 0 ≤ ∑ s, I.lam s u * x v s u :=
  Finset.sum_nonneg fun s _ => mul_nonneg (I.lam_nonneg s u) ((hx v).1 s u).1

lemma Iio_eq_Iic {t t' : Fin T} (h : (t : ℕ) = (t' : ℕ) + 1) : Finset.Iio t = Finset.Iic t' := by
  ext u
  simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_iff_val_le_val]
  omega

/-- (13)–(16): the load at `t` is at most `1 − q`, by constraint (2) at `t − 1`. -/
lemma slack_le (I : Instance V S T) (x : Decision V S T) (hx : x ∈ feasibleSet I) (v : Fin V)
    (t : Fin T) : slack I x v t ≤ 1 - mdhr I.g := by
  have hq1 := mdhr_le_one I
  rcases Nat.eq_zero_or_eq_succ_pred (t : ℕ) with h0 | hs
  · have : Finset.Iio t = ∅ := by
      ext u; simp only [Finset.mem_Iio, Fin.lt_def, Finset.notMem_empty, iff_false]; omega
    simp [slack, this]; linarith
  · set t' : Fin T := ⟨(t : ℕ) - 1, by omega⟩ with ht'
    have htt : (t : ℕ) = (t' : ℕ) + 1 := by simp [ht']; omega
    unfold slack
    rw [Iio_eq_Iic htt]
    have hrow := (hx v).2 t'
    calc ∑ u ∈ Finset.Iic t', (∑ s, I.lam s u * x v s u) * (1 - cdf I.g ((t : ℕ) - (u : ℕ)))
        ≤ ∑ u ∈ Finset.Iic t', (∑ s, I.lam s u * x v s u) *
            ((1 - mdhr I.g) * (1 - cdf I.g ((t' : ℕ) - (u : ℕ)))) := by
          refine Finset.sum_le_sum fun u hu => ?_
          refine mul_le_mul_of_nonneg_left ?_ (c_nonneg I x hx v u)
          have hu' : (u : ℕ) ≤ t' := Fin.le_iff_val_le_val.1 (Finset.mem_Iic.1 hu)
          have : (t : ℕ) - u = ((t' : ℕ) - u) + 1 := by omega
          rw [this]
          exact tail_step I _
      _ = (1 - mdhr I.g) * ∑ τ ∈ Finset.Iic t', ∑ s,
            I.lam s τ * x v s τ * (1 - cdf I.g ((t' : ℕ) - (τ : ℕ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ ≤ (1 - mdhr I.g) * 1 := mul_le_mul_of_nonneg_left hrow (by linarith)
      _ = 1 - mdhr I.g := mul_one _

end VNAux

open VolunteerNotify VNAux

theorem solution {V S T : ℕ} (I : Instance V S T) (xstar xt : Decision V S T)
    (J : Fin V → Fin (T + 1) → ℝ) (hx : IsExAnte I xstar) (hdp : IsDP I xstar xt J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Process I xt μ) :
    1 / (2 - mdhr I.g) * (1 - 1 / Real.exp 1) * lpValue I ≤ POL P := by
  have hq1 := mdhr_le_one I
  have hmu : 0 ≤ 1 / (2 - mdhr I.g) := by
    have : 0 < 2 - mdhr I.g := by linarith
    positivity
  calc 1 / (2 - mdhr I.g) * (1 - 1 / Real.exp 1) * lpValue I
      = 1 / (2 - mdhr I.g) * ((1 - 1 / Real.exp 1) * lpValue I) := by ring
    _ ≤ 1 / (2 - mdhr I.g) * f I xstar :=
        mul_le_mul_of_nonneg_left (proposition_2 I xstar hx) hmu
    _ ≤ POL P := closing_step I xstar xt J hx hdp μ P
