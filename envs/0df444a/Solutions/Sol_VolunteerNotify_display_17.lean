-- Prove2me | solution 1 for VolunteerNotify.display_17
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:15:23.269497+00:00
-- url     : https://prove2.me/submissions/32081218-5a71-4d94-9e03-62cdee41b014

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue
import Definitions.Def_VolunteerNotify_IsDP


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

namespace VNAux

open VolunteerNotify

/-- Summation by parts against the tail `1 − G`. -/
lemma parts (g : ℕ → ℝ) (hg0 : cdf g 0 = 0) (j : ℕ → ℝ) (a : ℕ) : ∀ m : ℕ,
    ∑ k ∈ Finset.range m, (1 - cdf g (k + 1)) * (j (a + 1 + k) - j (a + 2 + k)) =
      j (a + 1) - ∑ k ∈ Finset.range m, g (k + 1) * j (a + 1 + k) -
        (1 - cdf g m) * j (a + 1 + m) := by
  intro m
  induction m with
  | zero => simp [hg0]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cdf_succ]
    have e : a + 1 + (m + 1) = a + 2 + m := by omega
    rw [e]
    ring

lemma sum_Ioi_eq {T : ℕ} (t : Fin T) (F : ℕ → ℝ) :
    ∑ τ ∈ Finset.Ioi t, F τ = ∑ k ∈ Finset.range (T - 1 - t), F (t + 1 + k) := by
  symm
  refine Finset.sum_bij (fun k hk => (⟨(t : ℕ) + 1 + k, by
      have := Finset.mem_range.1 hk; omega⟩ : Fin T)) ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_Ioi, Fin.lt_def]
    omega
  · intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    omega
  · intro τ hτ
    have := Fin.lt_def.1 (Finset.mem_Ioi.1 hτ)
    refine ⟨(τ : ℕ) - t - 1, Finset.mem_range.2 (by omega), ?_⟩
    ext
    simp only
    omega
  · intro k _
    rfl

end VNAux

open VolunteerNotify VNAux

theorem solution {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : x ∈ feasibleSet I) (v : Fin V) (rbar : Fin S → Fin T → ℝ) (Jbar : Fin (T + 1) → ℝ)
    (hlast : Jbar (Fin.last T) = 0)
    (hα : ∀ t : Fin T, Jbar t.succ ≤ Jbar t.castSucc)
    (hγ : ∀ t : Fin T, Jbar t.succ +
      ∑ s, I.lam s t * x v s t * (rbar s t - Jbar t.succ + futureValue I Jbar t) ≤
        Jbar t.castSucc) :
    1 / (2 - mdhr I.g) * ∑ t, ∑ s, I.lam s t * rbar s t * x v s t ≤ Jbar 0 := by
  have hq1 := mdhr_le_one I
  have hpos : 0 < 2 - mdhr I.g := by linarith
  -- Read `J̄` as a sequence `j` on ℕ.
  obtain ⟨j, hj⟩ : ∃ j : ℕ → ℝ, ∀ i : Fin (T + 1), Jbar i = j i :=
    ⟨fun n => if h : n < T + 1 then Jbar ⟨n, h⟩ else 0, fun i => by dsimp only; rw [dif_pos i.isLt]⟩
  have hjT : j T = 0 := by rw [← hlast, hj]; simp
  have hD : ∀ t : Fin T, Jbar t.castSucc - Jbar t.succ = j t - j (t + 1) := by
    intro t; rw [hj, hj]; simp
  -- `J̄_1 = ∑_t (J̄_t − J̄_{t+1})`.
  have tele : Jbar 0 = ∑ t : Fin T, (Jbar t.castSucc - Jbar t.succ) := by
    simp only [hD]
    rw [Fin.sum_univ_eq_sum_range (fun n => j n - j (n + 1)) T, Finset.sum_range_sub', hjT,
      hj]
    simp
  -- `J̄_{t+1} − ∑_{τ>t} g(τ − t) J̄_τ = ∑_{τ>t} (1 − G(τ − t)) (J̄_τ − J̄_{τ+1})`.
  have hparts : ∀ t : Fin T, Jbar t.succ - futureValue I Jbar t =
      ∑ τ ∈ Finset.Ioi t, (1 - cdf I.g ((τ : ℕ) - (t : ℕ))) *
        (Jbar τ.castSucc - Jbar τ.succ) := by
    intro t
    unfold futureValue
    simp only [hD]
    have h1 := sum_Ioi_eq t (fun n => I.g (n - t) * j n)
    have h2 := sum_Ioi_eq t (fun n => (1 - cdf I.g (n - t)) * (j n - j (n + 1)))
    have hs : ∀ τ : Fin T, I.g ((τ : ℕ) - (t : ℕ)) * Jbar τ.castSucc = I.g (τ - t) * j τ := by
      intro τ; rw [hj]; simp
    simp only [hs]
    rw [h1, h2, hj]
    have e1 : ∀ k ∈ Finset.range (T - 1 - t),
        I.g ((t : ℕ) + 1 + k - t) * j (t + 1 + k) = I.g (k + 1) * j (t + 1 + k) := by
      intro k _; congr 2; omega
    have e2 : ∀ k ∈ Finset.range (T - 1 - t),
        (1 - cdf I.g ((t : ℕ) + 1 + k - t)) * (j (t + 1 + k) - j (t + 1 + k + 1)) =
          (1 - cdf I.g (k + 1)) * (j (t + 1 + k) - j (t + 2 + k)) := by
      intro k _
      have a1 : (t : ℕ) + 1 + k - t = k + 1 := by omega
      have a2 : (t : ℕ) + 1 + k + 1 = t + 2 + k := by omega
      rw [a1, a2]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, parts I.g (cdf_zero I) j t]
    have a3 : (t : ℕ) + 1 + (T - 1 - t) = T := by omega
    rw [a3, hjT]
    simp
  -- The γ-constraint at `t`: `R_t ≤ D_t + c_t ∑_{τ>t} (1 − G(τ − t)) D_τ`.
  have hR : ∀ t : Fin T, ∑ s, I.lam s t * rbar s t * x v s t ≤
      (Jbar t.castSucc - Jbar t.succ) + (∑ s, I.lam s t * x v s t) *
        ∑ τ ∈ Finset.Ioi t, (1 - cdf I.g ((τ : ℕ) - (t : ℕ))) *
          (Jbar τ.castSucc - Jbar τ.succ) := by
    intro t
    rw [← hparts t]
    have e : ∑ s, I.lam s t * x v s t * (rbar s t - Jbar t.succ + futureValue I Jbar t) =
        (∑ s, I.lam s t * rbar s t * x v s t) +
          (∑ s, I.lam s t * x v s t) * (futureValue I Jbar t - Jbar t.succ) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have := hγ t
    rw [e] at this
    linarith
  -- Exchange the order of summation: the inner sums become the loads `L_τ`.
  have hswap : ∑ t : Fin T, (∑ s, I.lam s t * x v s t) *
      ∑ τ ∈ Finset.Ioi t, (1 - cdf I.g ((τ : ℕ) - (t : ℕ))) * (Jbar τ.castSucc - Jbar τ.succ) =
      ∑ τ : Fin T, (Jbar τ.castSucc - Jbar τ.succ) * slack I x v τ := by
    simp only [Finset.mul_sum, slack]
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun τ => Finset.Iio τ)]
    · refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun u _ => ?_
      ring
    · intro a b
      simp [Finset.mem_Ioi, Finset.mem_Iio]
  have hsum : ∑ t, ∑ s, I.lam s t * rbar s t * x v s t ≤
      (2 - mdhr I.g) * ∑ t : Fin T, (Jbar t.castSucc - Jbar t.succ) := by
    calc ∑ t, ∑ s, I.lam s t * rbar s t * x v s t
        ≤ ∑ t : Fin T, ((Jbar t.castSucc - Jbar t.succ) + (∑ s, I.lam s t * x v s t) *
            ∑ τ ∈ Finset.Ioi t, (1 - cdf I.g ((τ : ℕ) - (t : ℕ))) *
              (Jbar τ.castSucc - Jbar τ.succ)) := Finset.sum_le_sum fun t _ => hR t
      _ = ∑ t : Fin T, (Jbar t.castSucc - Jbar t.succ) +
            ∑ τ : Fin T, (Jbar τ.castSucc - Jbar τ.succ) * slack I x v τ := by
          rw [Finset.sum_add_distrib, hswap]
      _ ≤ ∑ t : Fin T, (Jbar t.castSucc - Jbar t.succ) +
            ∑ τ : Fin T, (Jbar τ.castSucc - Jbar τ.succ) * (1 - mdhr I.g) := by
          gcongr with τ
          · exact sub_nonneg.2 (hα τ)
          · exact slack_le I x hx v τ
      _ = (2 - mdhr I.g) * ∑ t : Fin T, (Jbar t.castSucc - Jbar t.succ) := by
          rw [← Finset.sum_mul]
          ring
  rw [tele, div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  linarith
