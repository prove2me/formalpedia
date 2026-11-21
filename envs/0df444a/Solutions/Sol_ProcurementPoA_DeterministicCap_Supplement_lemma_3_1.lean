-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:31:23.957827+00:00
-- url     : https://prove2.me/submissions/5f1c27f4-7464-47cf-ae6e-112762d171b7

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction

section
set_option autoImplicit false

open Filter Topology

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

noncomputable def Kf (c : Fin (n + 1) → ℝ) (b : ℝ) : ℝ := (1 / (n : ℝ)) * ∑ k, 1 / (b - c k)

noncomputable def kap (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (b : ℝ) : ℝ :=
  Kf c b - 1 / (b - c i)

noncomputable def Hf (c : Fin (n + 1) → ℝ) (L b : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ k, (Real.log (L - c k) - Real.log (b - c k))

noncomputable def Ff (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) : ℝ :=
  Real.log (b - c i) - Real.log (L - c i) + Hf c L b

noncomputable def Sf (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) : ℝ :=
  Real.exp (Ff c L i b)

noncomputable def Qf (c : Fin (n + 1) → ℝ) (L b : ℝ) : ℝ := Real.exp (Hf c L b)

lemma hasDerivAt_Hf (c : Fin (n + 1) → ℝ) (L b : ℝ) (hb : ∀ k, c k < b) :
    HasDerivAt (Hf c L) (-(Kf c b)) b := by
  have h : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))),
      HasDerivAt (fun y : ℝ => Real.log (L - c k) - Real.log (y - c k)) (-(1 / (b - c k))) b := by
    intro k _
    have h1 : HasDerivAt (fun y : ℝ => y - c k) 1 b := (hasDerivAt_id b).sub_const _
    exact (h1.log (sub_ne_zero.2 (hb k).ne')).const_sub _ |>.congr_deriv (by simp)
  have h3 := (HasDerivAt.fun_sum h).const_mul (1 / (n : ℝ))
  show HasDerivAt (fun y => (1 / (n : ℝ)) * ∑ k, (Real.log (L - c k) - Real.log (y - c k)))
    (-(Kf c b)) b
  refine h3.congr_deriv ?_
  unfold Kf
  rw [Finset.sum_neg_distrib]; ring

lemma hasDerivAt_Sf (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) (hb : ∀ k, c k < b) :
    HasDerivAt (Sf c L i) (-(Sf c L i b * kap c i b)) b := by
  have h1 : HasDerivAt (fun y : ℝ => y - c i) 1 b := (hasDerivAt_id b).sub_const _
  have h2 := h1.log (sub_ne_zero.2 (hb i).ne')
  have h3 : HasDerivAt (fun y => Real.log (y - c i) - Real.log (L - c i) + Hf c L y)
      (1 / (b - c i) + -Kf c b) b :=
    (h2.sub_const (Real.log (L - c i))).add (hasDerivAt_Hf c L b hb) |>.congr_deriv (by simp)
  have h4 := h3.exp
  show HasDerivAt (fun y => Real.exp (Real.log (y - c i) - Real.log (L - c i) + Hf c L y)) _ b
  refine h4.congr_deriv ?_
  unfold Sf Ff kap
  ring

lemma hasDerivAt_Qf (c : Fin (n + 1) → ℝ) (L : ℝ) (b : ℝ) (hb : ∀ k, c k < b) :
    HasDerivAt (Qf c L) (-(Qf c L b * Kf c b)) b := by
  have := (hasDerivAt_Hf c L b hb).exp
  show HasDerivAt (fun y => Real.exp (Hf c L y)) _ b
  refine this.congr_deriv ?_
  unfold Qf
  ring

lemma Sf_L (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) : Sf c L i L = 1 := by
  simp [Sf, Ff, Hf]

lemma Qf_L (c : Fin (n + 1) → ℝ) (L : ℝ) : Qf c L L = 1 := by
  simp [Qf, Hf]

lemma Sf_pos (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) : 0 < Sf c L i b :=
  Real.exp_pos _

lemma Qf_pos (c : Fin (n + 1) → ℝ) (L b : ℝ) : 0 < Qf c L b := Real.exp_pos _

/-- identity: the product of the others' survival functions -/
lemma prod_Sf (c : Fin (n + 1) → ℝ) (L : ℝ) (hn : 1 ≤ n) (i : Fin (n + 1)) (b : ℝ)
    (hb : ∀ k, c k < b) (hL : ∀ k, c k < L) :
    ∏ j ∈ Finset.univ.erase i, Sf c L j b = (L - c i) / (b - c i) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hcard : (Finset.univ.erase i).card = n := by simp
  unfold Sf
  rw [← Real.exp_sum]
  have e : ∑ j ∈ Finset.univ.erase i, Ff c L j b =
      Real.log (L - c i) - Real.log (b - c i) := by
    unfold Ff
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    have hH : (n : ℝ) * Hf c L b = ∑ j, (Real.log (L - c j) - Real.log (b - c j)) := by
      unfold Hf; field_simp
    have a1 := Finset.add_sum_erase Finset.univ
      (fun j => (Real.log (L - c j) - Real.log (b - c j))) (Finset.mem_univ i)
    have a2 := Finset.add_sum_erase Finset.univ
      (fun j => (Real.log (b - c j) - Real.log (L - c j))) (Finset.mem_univ i)
    have a3 : ∑ j, (Real.log (b - c j) - Real.log (L - c j)) =
        -∑ j, (Real.log (L - c j) - Real.log (b - c j)) := by
      rw [← Finset.sum_neg_distrib]; congr 1; ext; ring
    linarith
  rw [e, Real.exp_sub, Real.exp_log (sub_pos.2 (hL i)), Real.exp_log (sub_pos.2 (hb i))]

noncomputable def Bnd (c : Fin (n + 1) → ℝ) : ℝ := ∑ k, |c k|

lemma abs_le_Bnd (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : |c k| ≤ Bnd c :=
  Finset.single_le_sum (f := fun k => |c k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)

lemma Bnd_nonneg (c : Fin (n + 1) → ℝ) : 0 ≤ Bnd c :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma kap_nonneg (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (i : Fin (n + 1)) (b : ℝ)
    (hb : (2 * n + 1) * Bnd c + 1 ≤ b) : 0 ≤ kap c i b := by
  have hB := Bnd_nonneg c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbB : Bnd c < b := by nlinarith
  have hpos : 0 < b - Bnd c := by linarith
  have hk : ∀ k, 1 / (b + Bnd c) ≤ 1 / (b - c k) := by
    intro k
    have := abs_le_Bnd c k
    have := neg_abs_le (c k)
    have := le_abs_self (c k)
    apply one_div_le_one_div_of_le (by linarith) (by linarith)
  have hsum : ((n : ℝ) + 1) * (1 / (b + Bnd c)) ≤ ∑ k, 1 / (b - c k) := by
    have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)
    simpa using this
  have hi : 1 / (b - c i) ≤ 1 / (b - Bnd c) := by
    have := abs_le_Bnd c i
    have := le_abs_self (c i)
    apply one_div_le_one_div_of_le hpos (by linarith)
  unfold kap Kf
  have h1 : 1 / (b - Bnd c) ≤ (1 / (n : ℝ)) * (((n : ℝ) + 1) * (1 / (b + Bnd c))) := by
    rw [div_le_iff₀ hpos]
    have hbp : 0 < b + Bnd c := by linarith
    field_simp
    nlinarith
  have h2 : (1 / (n : ℝ)) * (((n : ℝ) + 1) * (1 / (b + Bnd c))) ≤
      (1 / (n : ℝ)) * ∑ k, 1 / (b - c k) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  linarith

lemma sum_kap (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (b : ℝ) : ∑ i, kap c i b = Kf c b := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold kap
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Kf
  push_cast
  field_simp
  ring

lemma Qf_le_Sf (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ)
    (hL : ∀ k, c k < L) (hLb : L ≤ b) : Qf c L b ≤ Sf c L i b := by
  unfold Sf Qf Ff
  rw [Real.exp_add]
  have h1 : 1 ≤ Real.exp (Real.log (b - c i) - Real.log (L - c i)) := by
    apply Real.one_le_exp
    have := Real.log_le_log (sub_pos.2 (hL i)) (by linarith : L - c i ≤ b - c i)
    linarith
  have := Real.exp_pos (Hf c L b)
  nlinarith

lemma kap_le (c : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (b : ℝ) (hb : Bnd c < b) :
    kap c i b ≤ kap c j b + 2 * Bnd c / (b - Bnd c) ^ 2 := by
  have hB := Bnd_nonneg c
  have ci := abs_le_Bnd c i
  have cj := abs_le_Bnd c j
  have ci1 := le_abs_self (c i)
  have cj1 := le_abs_self (c j)
  have ci2 := neg_abs_le (c i)
  have cj2 := neg_abs_le (c j)
  have hx : 0 < b - c j := by linarith
  have hy : 0 < b - c i := by linarith
  have ht : 0 < b - Bnd c := by linarith
  have e : kap c i b - kap c j b = 1 / (b - c j) - 1 / (b - c i) := by unfold kap; ring
  have : 1 / (b - c j) - 1 / (b - c i) ≤ 2 * Bnd c / (b - Bnd c) ^ 2 := by
    rw [div_sub_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hxy : (b - Bnd c) ^ 2 ≤ (b - c j) * (b - c i) := by nlinarith
    nlinarith [mul_pos hx hy]
  linarith

lemma Sf_tendsto (c : Fin (n + 1) → ℝ) (L : ℝ) (hn : 1 ≤ n) (i : Fin (n + 1))
    (hLB : Bnd c < L) : Tendsto (Sf c L i) atTop (𝓝 0) := by
  have hB := Bnd_nonneg c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set B := Bnd c with hBdef
  set C0 : ℝ := -Real.log (L - c i) + (1 / (n : ℝ)) * ∑ k, Real.log (L - c k) with hC0
  let g : ℝ → ℝ := fun b => (Real.log (b + B) - Real.log (b - B)) +
    (-(1 / (n : ℝ)) * Real.log (b - B) + C0)
  have hg1 : Tendsto (fun b : ℝ => Real.log (b + B) - Real.log (b - B)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun b : ℝ => (b + B) / (b - B)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun b : ℝ => 2 * B / (b - B)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
      have := h2.const_add 1
      simp only [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop B] with b hb
      have : b - B ≠ 0 := by linarith
      field_simp
      ring
    have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    simp only [Real.log_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop B] with b hb
    simp only [Function.comp]
    rw [Real.log_div (by linarith) (by linarith)]
  have hg2 : Tendsto (fun b : ℝ => -(1 / (n : ℝ)) * Real.log (b - B) + C0) atTop atBot := by
    have h1 : Tendsto (fun b : ℝ => Real.log (b - B)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 : Tendsto (fun b : ℝ => -(1 / (n : ℝ)) * Real.log (b - B)) atTop atBot :=
      h1.const_mul_atTop_of_neg (by have : (0:ℝ) < 1 / n := by positivity
                                    linarith)
    exact tendsto_atBot_add_const_right _ _ h2
  have hg : Tendsto g atTop atBot := hg1.add_atBot hg2
  have hle : ∀ᶠ b in atTop, Ff c L i b ≤ g b := by
    filter_upwards [eventually_ge_atTop L] with b hb
    have hbB : B < b := by linarith
    have hci := abs_le_Bnd c i
    have h1 : Real.log (b - c i) ≤ Real.log (b + B) :=
      Real.log_le_log (by linarith [le_abs_self (c i)]) (by linarith [neg_abs_le (c i)])
    have h2 : ∀ k, Real.log (b - B) ≤ Real.log (b - c k) := fun k =>
      Real.log_le_log (by linarith) (by linarith [le_abs_self (c k), abs_le_Bnd c k])
    have h3 : ((n : ℝ) + 1) * Real.log (b - B) ≤ ∑ k, Real.log (b - c k) := by
      have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h2 k)
      simpa using this
    have hH : Hf c L b ≤ (1 / (n : ℝ)) * (∑ k, Real.log (L - c k) - ((n : ℝ) + 1) * Real.log (b - B)) := by
      unfold Hf
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.sum_sub_distrib]
      linarith
    unfold Ff
    have : (1 / (n : ℝ)) * (∑ k, Real.log (L - c k) - ((n : ℝ) + 1) * Real.log (b - B))
        = C0 + Real.log (L - c i) - ((n : ℝ) + 1) / n * Real.log (b - B) := by
      rw [hC0]; field_simp; ring
    have e : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
    simp only [g]
    rw [e] at this
    nlinarith
  have hF : Tendsto (Ff c L i) atTop atBot := tendsto_atBot_mono' _ hle hg
  exact Real.tendsto_exp_atBot.comp hF

lemma Qf_tendsto (c : Fin (n + 1) → ℝ) (L : ℝ) (hn : 1 ≤ n)
    (hL : ∀ k, c k < L) (hLB : Bnd c < L) : Tendsto (Qf c L) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Sf_tendsto c L hn 0 hLB) (Eventually.of_forall fun b => (Qf_pos c L b).le) ?_
  filter_upwards [eventually_ge_atTop L] with b hb
  exact Qf_le_Sf c L 0 b hL hb

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

variable {n : ℕ}

/-- product over the other suppliers, in `succAbove` form -/
noncomputable def Pr (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) : ℝ :=
  ∏ j : Fin n, Sf c L (i.succAbove j) b

lemma Pr_eq (c : Fin (n + 1) → ℝ) (L : ℝ) (hn : 1 ≤ n) (i : Fin (n + 1)) (b : ℝ)
    (hb : ∀ k, c k < b) (hL : ∀ k, c k < L) :
    Pr c L i b = (L - c i) / (b - c i) := by
  have h1 := Fin.prod_univ_succAbove (fun k => Sf c L k b) i
  have h2 := Finset.mul_prod_erase Finset.univ (fun k => Sf c L k b) (Finset.mem_univ i)
  have h3 := prod_Sf c L hn i b hb hL
  have hpos := Sf_pos c L i b
  unfold Pr
  have : Sf c L i b * ∏ j : Fin n, Sf c L (i.succAbove j) b = Sf c L i b * ∏ j ∈ Finset.univ.erase i, Sf c L j b := by
    rw [← h1, ← h2]
  rw [mul_left_cancel₀ hpos.ne' this]
  exact h3

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
end

section
set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31B

variable {n : ℕ}

structure Good (c : Fin (n + 1) → ℝ) (L : ℝ) : Prop where
  hn : 1 ≤ n
  hL : (2 * n + 1) * Bnd c + 1 ≤ L

lemma Good.Bnd_lt {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) : Bnd c < L := by
  have := Bnd_nonneg c
  have hh := h.hL
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma Good.lt {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (k : Fin (n + 1)) : c k < L :=
  lt_of_le_of_lt ((le_abs_self _).trans (abs_le_Bnd c k)) h.Bnd_lt

lemma Good.lt_of_le {c : Fin (n + 1) → ℝ} {L b : ℝ} (h : Good c L) (hb : L ≤ b)
    (k : Fin (n + 1)) : c k < b := lt_of_lt_of_le (h.lt k) hb

noncomputable def dens (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (b : ℝ) : ℝ≥0∞ :=
  if L < b then ENNReal.ofReal (Sf c L i b * kap c i b) else 0

noncomputable def mu (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) : Measure ℝ :=
  volume.withDensity (dens c L i)

lemma mu_Ioi {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i : Fin (n + 1)) {b : ℝ}
    (hb : L ≤ b) : mu c L i (Ioi b) = ENNReal.ofReal (Sf c L i b) := by
  rw [mu, withDensity_apply _ measurableSet_Ioi]
  have e : ∫⁻ x in Ioi b, dens c L i x = ∫⁻ x in Ioi b, ENNReal.ofReal (Sf c L i x * kap c i x) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [dens, lt_of_le_of_lt hb hx]
  rw [e]
  have hderiv : ∀ x ∈ Ioi b, HasDerivAt (fun y => -Sf c L i y) (Sf c L i x * kap c i x) x := by
    intro x hx
    exact (hasDerivAt_Sf c L i x (h.lt_of_le (hb.trans hx.out.le))).neg.congr_deriv (neg_neg _)
  have hnn : ∀ x ∈ Ioi b, 0 ≤ Sf c L i x * kap c i x := by
    intro x hx
    exact mul_nonneg (Sf_pos c L i x).le
      (kap_nonneg c h.hn i x (h.hL.trans (hb.trans hx.out.le)))
  have hcont : ContinuousWithinAt (fun y => -Sf c L i y) (Ici b) b :=
    (hasDerivAt_Sf c L i b (h.lt_of_le hb)).neg.continuousAt.continuousWithinAt
  have htend : Tendsto (fun y => -Sf c L i y) atTop (𝓝 (-0)) :=
    (Sf_tendsto c L h.hn i h.Bnd_lt).neg
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
  have hI := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)), hint]
  simp

lemma mu_Iic {c : Fin (n + 1) → ℝ} {L : ℝ} (i : Fin (n + 1)) : mu c L i (Iic L) = 0 := by
  rw [mu, withDensity_apply _ measurableSet_Iic]
  rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)]
  · simp
  · intro x hx
    simp [dens, not_lt.2 (mem_Iic.1 hx)]

lemma mu_isProb {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i : Fin (n + 1)) :
    IsProbabilityMeasure (mu c L i) := by
  refine ⟨?_⟩
  have e : (univ : Set ℝ) = Iic L ∪ Ioi L := (Set.Iic_union_Ioi).symm
  rw [e, measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, mu_Iic,
    mu_Ioi h i le_rfl, Sf_L]
  simp

lemma mu_noAtoms {c : Fin (n + 1) → ℝ} {L : ℝ} (i : Fin (n + 1)) : NullSingletonClass (mu c L i) :=
  ⟨fun x => withDensity_absolutelyContinuous _ _ (Real.volume_singleton)⟩

lemma mu_Ici {c : Fin (n + 1) → ℝ} {L : ℝ} (i : Fin (n + 1)) (b : ℝ) :
    mu c L i (Ici b) = mu c L i (Ioi b) := by
  haveI := mu_noAtoms (c := c) (L := L) i
  exact (measure_congr Ioi_ae_eq_Ici).symm

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
open ProcurementPoA.DeterministicCap

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31C

variable {n : ℕ}

lemma sel_one (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∀ j, j ≠ i → v i < v j) : τ.select v {i} = 1 := by
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k = i := by
    filter_upwards [h1] with k hk
    by_contra hki
    have := hk i
    exact absurd (h k hki) (not_lt.2 this)
  have h3 : ({i} : Set (Suppliers n)) =ᵐ[τ.select v] (univ : Set (Suppliers n)) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [h2] with k hk
    simp [hk]
  rw [measure_congr h3, measure_univ]

lemma sel_zero (τ : TieRule n) (v : Suppliers n → ℝ) (i : Suppliers n)
    (h : ∃ j, v j < v i) : τ.select v {i} = 0 := by
  obtain ⟨j, hj⟩ := h
  have h1 := τ.lowest_only v
  have h2 : ∀ᵐ k ∂(τ.select v), k ≠ i := by
    filter_upwards [h1] with k hk hki
    subst hki
    exact absurd (hk j) (not_le.2 hj)
  exact measure_mono_null (fun k hk => not_not.2 (mem_singleton_iff.1 hk)) (ae_iff.1 h2)

lemma const_comp_dirac (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    (Kernel.const ℝ ν) ∘ₘ (Measure.dirac x) = ν := by
  exact (Measure.dirac_bind (Kernel.measurable _) x).trans (by simp)

noncomputable def sigP {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) : MixedProfile n where
  bid i := Kernel.const ℝ (mu c L i)
  markov i := by
    haveI := mu_isProb h i
    infer_instance

lemma marg {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (j : Suppliers n) :
    marginalBidLaw (deterministicTypes c) (sigP h) j = mu c L j := by
  haveI := mu_isProb h j
  unfold marginalBidLaw
  simp only [sigP, deterministicTypes]
  exact const_comp_dirac _ _

lemma box_measure {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i : Suppliers n) (A : Set ℝ)
    (hA : MeasurableSet A) :
    Measure.pi (fun j => mu c L j) (Set.pi univ (fun k => if k = i then univ else A))
      = ∏ j : Fin n, mu c L (i.succAbove j) A := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  rw [Measure.pi_pi, Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

lemma interimWin_ge {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n)
    (i : Suppliers n) (b : ℝ) :
    ∏ j : Fin n, mu c L (i.succAbove j) (Ioi b) ≤
      interimWin (deterministicTypes c) τ (sigP h) i b := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  unfold interimWin
  have hm : marginalBidLaw (deterministicTypes c) (sigP h) = fun j => mu c L j :=
    funext (marg h)
  rw [hm, ← box_measure h i (Ioi b) measurableSet_Ioi]
  have hmeas : MeasurableSet (Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)) :=
    MeasurableSet.univ_pi fun k => by by_cases hk : k = i <;> simp [hk, measurableSet_Ioi]
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_mono
  intro bs
  by_cases hbs : bs ∈ Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ioi b)
  · rw [Set.indicator_of_mem hbs]
    simp only [Pi.one_apply]
    rw [sel_one τ _ i]
    intro j hj
    have := hbs j (mem_univ j)
    simp only [hj, if_false, mem_Ioi] at this
    simp [Function.update_self, Function.update_of_ne hj, this]
  · rw [Set.indicator_of_notMem hbs]; exact zero_le

lemma interimWin_le {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n)
    (i : Suppliers n) (b : ℝ) :
    interimWin (deterministicTypes c) τ (sigP h) i b ≤
      ∏ j : Fin n, mu c L (i.succAbove j) (Ici b) := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  unfold interimWin
  have hm : marginalBidLaw (deterministicTypes c) (sigP h) = fun j => mu c L j :=
    funext (marg h)
  rw [hm, ← box_measure h i (Ici b) measurableSet_Ici]
  have hmeas : MeasurableSet (Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ici b)) :=
    MeasurableSet.univ_pi fun k => by by_cases hk : k = i <;> simp [hk, measurableSet_Ici]
  rw [← lintegral_indicator_one hmeas]
  apply lintegral_mono
  intro bs
  by_cases hbs : bs ∈ Set.pi univ (fun k : Suppliers n => if k = i then (univ : Set ℝ) else Ici b)
  · rw [Set.indicator_of_mem hbs]
    simp only [Pi.one_apply]
    exact prob_le_one
  · rw [Set.indicator_of_notMem hbs]
    have : ∃ j, Function.update bs i b j < Function.update bs i b i := by
      by_contra hcon
      push_neg at hcon
      apply hbs
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · simp only [hj, if_false, mem_Ici]
        have := hcon j
        simpa [Function.update_self, Function.update_of_ne hj] using this
    simp only
    rw [sel_zero τ _ i this]

lemma win_prod_eq {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i : Suppliers n) {b : ℝ}
    (hb : L ≤ b) :
    ∏ j : Fin n, mu c L (i.succAbove j) (Ioi b) = ENNReal.ofReal ((L - c i) / (b - c i)) := by
  have e : ∀ j : Fin n, mu c L (i.succAbove j) (Ioi b) =
      ENNReal.ofReal (Sf c L (i.succAbove j) b) := fun j => mu_Ioi h _ hb
  simp_rw [e]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Sf_pos c L _ b).le)]
  congr 1
  exact Pr_eq c L h.hn i b (h.lt_of_le hb) h.lt

lemma interimWin_eq {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n)
    (i : Suppliers n) {b : ℝ} (hb : L ≤ b) :
    interimWin (deterministicTypes c) τ (sigP h) i b = ENNReal.ofReal ((L - c i) / (b - c i)) := by
  apply le_antisymm
  · refine (interimWin_le h τ i b).trans ?_
    have e : ∀ j : Fin n, mu c L (i.succAbove j) (Ici b) = mu c L (i.succAbove j) (Ioi b) :=
      fun j => mu_Ici _ _
    simp_rw [e]
    exact (win_prod_eq h i hb).le
  · rw [← win_prod_eq h i hb]
    exact interimWin_ge h τ i b

lemma interimWin_le_one {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n)
    (i : Suppliers n) (b : ℝ) : interimWin (deterministicTypes c) τ (sigP h) i b ≤ 1 := by
  unfold interimWin
  calc _ ≤ ∫⁻ _bs, (1 : ℝ≥0∞) ∂(Measure.pi (marginalBidLaw (deterministicTypes c) (sigP h))) :=
        lintegral_mono fun _ => prob_le_one
    _ = 1 := by simp

theorem isBNE {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) :
    IsStandardBNE (deterministicTypes c) τ (sigP h) := by
  have hnu : ∀ i, ∀ᵐ b ∂(mu c L i), L < b := by
    intro i
    have := mu_Iic (c := c) (L := L) i
    filter_upwards [(measure_eq_zero_iff_ae_notMem.1 this)] with b hb
    exact not_le.1 hb
  refine ⟨?_, fun i c' _ => Eventually.of_forall fun _ => mem_univ _, ?_⟩
  · intro i c' hc'
    simp only [deterministicTypes, mem_singleton_iff] at hc'
    subst hc'
    rw [show (sigP h).bid i (c i) = mu c L i from rfl]
    filter_upwards [hnu i] with b hb
    exact (h.lt i).le.trans hb.le
  · intro i c' hc'
    simp only [deterministicTypes, mem_singleton_iff] at hc'
    subst hc'
    rw [show (sigP h).bid i (c i) = mu c L i from rfl]
    filter_upwards [hnu i] with b hb a _
    have hci := h.lt i
    have hbc : 0 < b - c i := by linarith
    have hUb : standardUtility (deterministicTypes c) τ (sigP h) i (c i) b = L - c i := by
      unfold standardUtility
      rw [interimWin_eq h τ i hb.le, ENNReal.toReal_ofReal (by positivity)]
      field_simp
    rw [hUb]
    unfold standardUtility
    by_cases haL : L ≤ a
    · rw [interimWin_eq h τ i haL]
      have : 0 < a - c i := by linarith
      rw [ENNReal.toReal_ofReal (by positivity)]
      field_simp
      exact le_rfl
    · push_neg at haL
      have h1 : (interimWin (deterministicTypes c) τ (sigP h) i a).toReal ≤ 1 := by
        have := interimWin_le_one h τ i a
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      have h0 := ENNReal.toReal_nonneg (a := interimWin (deterministicTypes c) τ (sigP h) i a)
      by_cases hac : 0 ≤ a - c i
      · nlinarith
      · nlinarith

lemma playLaw_map {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) :
    (playLaw (deterministicTypes c) (sigP h)).map (fun (x : Suppliers n → ℝ × ℝ) j => (x j).2)
      = Measure.pi (fun j => mu c L j) := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  unfold playLaw
  rw [Measure.pi_map_pi (f := fun _ => (Prod.snd : ℝ × ℝ → ℝ)) (fun j => measurable_snd.aemeasurable)]
  congr 1
  ext1 j
  show ((deterministicTypes c).law j ⊗ₘ (sigP h).bid j).snd = _
  rw [Measure.snd_compProd]
  exact const_comp_dirac _ _

lemma winProb_eq {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) (i : Suppliers n) :
    winProbability (deterministicTypes c) τ (sigP h) i =
      ∫⁻ bs, τ.select bs {i} ∂(Measure.pi (fun j => mu c L j)) := by
  unfold winProbability
  have hg : Measurable (fun (x : Suppliers n → ℝ × ℝ) j => (x j).2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_pi_apply j))
  rw [← playLaw_map h]
  exact (lintegral_map (Kernel.measurable_coe τ.select (measurableSet_singleton i)) hg).symm

lemma pi_E {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i : Suppliers n) :
    Measure.pi (fun j => mu c L j) {bs | ∀ j, j ≠ i → bs i < bs j} =
      ∫⁻ x, ∏ j : Fin n, mu c L (i.succAbove j) (Ioi x) ∂(mu c L i) := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  have hmp := measurePreserving_piFinSuccAbove (fun j => mu c L j) i
  set T : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j, p.1 < p.2 j} with hT
  have hTm : MeasurableSet T := by
    have : T = ⋂ j, {p : ℝ × (Fin n → ℝ) | p.1 < p.2 j} := by ext; simp [hT]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  have e : {bs : Suppliers n → ℝ | ∀ j, j ≠ i → bs i < bs j} =
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' T := by
    ext bs
    simp only [mem_setOf_eq, mem_preimage, hT, MeasurableEquiv.piFinSuccAbove_apply]
    constructor
    · intro hbs j
      exact hbs _ (Fin.succAbove_ne i j)
    · intro hbs j hj
      obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact hbs j'
  rw [e, hmp.measure_preimage_equiv, Measure.prod_apply hTm]
  congr 1
  ext1 x
  have : Prod.mk x ⁻¹' T = Set.pi univ (fun _ : Fin n => Ioi x) := by
    ext r; simp [hT]
  rw [this, Measure.pi_pi]

lemma Sf_mul_w (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) (x : ℝ) (hx : c i < x)
    (hL : c i < L) : Sf c L i x * ((L - c i) / (x - c i)) = Qf c L x := by
  unfold Sf Ff Qf
  rw [Real.exp_add, Real.exp_sub, Real.exp_log (sub_pos.2 hx), Real.exp_log (sub_pos.2 hL)]
  have : x - c i ≠ 0 := (sub_pos.2 hx).ne'
  have : L - c i ≠ 0 := (sub_pos.2 hL).ne'
  field_simp

lemma meas_dens (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) : Measurable (dens c L i) := by
  have h1 : Measurable (fun b : ℝ => Sf c L i b * kap c i b) := by
    unfold Sf Ff Hf kap Kf
    fun_prop
  exact Measurable.ite measurableSet_Ioi (ENNReal.measurable_ofReal.comp h1) measurable_const

lemma mu_ae_gt {c : Fin (n + 1) → ℝ} {L : ℝ} (i : Fin (n + 1)) : ∀ᵐ b ∂(mu c L i), L < b := by
  have := mu_Iic (c := c) (L := L) i
  filter_upwards [(measure_eq_zero_iff_ae_notMem.1 this)] with b hb
  exact not_le.1 hb

noncomputable def Pi_ (c : Fin (n + 1) → ℝ) (L : ℝ) (i : Fin (n + 1)) : ℝ≥0∞ :=
  ∫⁻ x in Ioi L, ENNReal.ofReal (Qf c L x * kap c i x)

lemma winProb_ge {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) (i : Suppliers n) :
    Pi_ c L i ≤ winProbability (deterministicTypes c) τ (sigP h) i := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  rw [winProb_eq h τ i]
  have hEm : MeasurableSet {bs : Suppliers n → ℝ | ∀ j, j ≠ i → bs i < bs j} := by
    have : {bs : Suppliers n → ℝ | ∀ j, j ≠ i → bs i < bs j} =
        ⋂ j, ⋂ (_ : j ≠ i), {bs | bs i < bs j} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  have h1 : Measure.pi (fun j => mu c L j) {bs | ∀ j, j ≠ i → bs i < bs j} ≤
      ∫⁻ bs, τ.select bs {i} ∂(Measure.pi (fun j => mu c L j)) := by
    rw [← lintegral_indicator_one hEm]
    apply lintegral_mono
    intro bs
    by_cases hbs : bs ∈ {bs : Suppliers n → ℝ | ∀ j, j ≠ i → bs i < bs j}
    · rw [Set.indicator_of_mem hbs]
      simp only [Pi.one_apply]
      rw [sel_one τ bs i hbs]
    · rw [Set.indicator_of_notMem hbs]; exact zero_le
  refine le_trans ?_ h1
  rw [pi_E h]
  have h2 : ∫⁻ x, ENNReal.ofReal ((L - c i) / (x - c i)) ∂(mu c L i) ≤
      ∫⁻ x, ∏ j : Fin n, mu c L (i.succAbove j) (Ioi x) ∂(mu c L i) := by
    apply lintegral_mono_ae
    filter_upwards [mu_ae_gt (c := c) i] with x hx
    rw [win_prod_eq h i hx.le]
  refine le_trans ?_ h2
  have hw : Measurable (fun x : ℝ => ENNReal.ofReal ((L - c i) / (x - c i))) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  rw [mu, lintegral_withDensity_eq_lintegral_mul volume (meas_dens c L i) hw]
  unfold Pi_
  rw [← lintegral_indicator measurableSet_Ioi]
  apply le_of_eq
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Ioi L
  · rw [Set.indicator_of_mem hx]
    have hx' : L < x := hx
    simp only [Pi.mul_apply, dens, if_pos hx']
    rw [← ENNReal.ofReal_mul (mul_nonneg (Sf_pos c L i x).le
      (kap_nonneg c h.hn i x (h.hL.trans hx'.le)))]
    congr 1
    rw [← Sf_mul_w c L i x (h.lt_of_le hx'.le i) (h.lt i)]
    ring
  · rw [Set.indicator_of_notMem hx]
    simp only [Pi.mul_apply, dens, if_neg (show ¬ L < x from hx), zero_mul]

lemma sum_select {n : ℕ} (τ : TieRule n) (b : Suppliers n → ℝ) : ∑ i, τ.select b {i} = 1 := by
  rw [sum_measure_singleton]; simp

lemma sum_win {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) :
    ∑ i, winProbability (deterministicTypes c) τ (sigP h) i = 1 := by
  haveI : ∀ j, IsProbabilityMeasure (mu c L j) := fun j => mu_isProb h j
  simp_rw [winProb_eq h τ]
  rw [← lintegral_finset_sum _ (fun i _ => Kernel.measurable_coe τ.select (measurableSet_singleton i))]
  simp_rw [sum_select]
  simp

lemma Kf_nonneg (c : Fin (n + 1) → ℝ) {x : ℝ} (hx : ∀ k, c k < x) : 0 ≤ Kf c x := by
  unfold Kf
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun k _ => (one_div_pos.2 (sub_pos.2 (hx k))).le)

lemma sum_Pi {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) : ∑ i, Pi_ c L i = 1 := by
  unfold Pi_
  have hm : ∀ i : Fin (n + 1), Measurable (fun x : ℝ => ENNReal.ofReal (Qf c L x * kap c i x)) := by
    intro i
    apply ENNReal.measurable_ofReal.comp
    unfold Qf Hf kap Kf
    fun_prop
  rw [← lintegral_finset_sum _ (fun i _ => hm i)]
  have e : ∫⁻ x in Ioi L, ∑ i, ENNReal.ofReal (Qf c L x * kap c i x) =
      ∫⁻ x in Ioi L, ENNReal.ofReal (Qf c L x * Kf c x) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : L < x := hx
    show ∑ i, ENNReal.ofReal (Qf c L x * kap c i x) = ENNReal.ofReal (Qf c L x * Kf c x)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Qf_pos c L x).le
      (kap_nonneg c h.hn i x (h.hL.trans hx'.le))), ← Finset.mul_sum, sum_kap c h.hn]
  rw [e]
  have hderiv : ∀ x ∈ Ioi L, HasDerivAt (fun y => -Qf c L y) (Qf c L x * Kf c x) x := by
    intro x hx
    exact (hasDerivAt_Qf c L x (h.lt_of_le (le_of_lt hx))).neg.congr_deriv (neg_neg _)
  have hnn : ∀ x ∈ Ioi L, 0 ≤ Qf c L x * Kf c x := fun x hx =>
    mul_nonneg (Qf_pos c L x).le (Kf_nonneg c (h.lt_of_le (le_of_lt hx)))
  have hcont : ContinuousWithinAt (fun y => -Qf c L y) (Ici L) L :=
    (hasDerivAt_Qf c L L (h.lt)).neg.continuousAt.continuousWithinAt
  have htend : Tendsto (fun y => -Qf c L y) atTop (𝓝 (-0)) :=
    (Qf_tendsto c L h.hn h.lt h.Bnd_lt).neg
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
  have hI := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)), hint]
  simp [Qf_L]

lemma win_eq_Pi {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) (i : Suppliers n) :
    winProbability (deterministicTypes c) τ (sigP h) i = Pi_ c L i := by
  have hge := fun j => winProb_ge h τ j
  have hs := sum_win h τ
  have hP := sum_Pi h
  have hfin : ∀ j, winProbability (deterministicTypes c) τ (sigP h) j ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => winProbability (deterministicTypes c) τ (sigP h) j)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have hPfin : ∀ j, Pi_ c L j ≠ ⊤ := fun j => ne_top_of_le_ne_top (hfin j) (hge j)
  have h1 : ∑ j, (winProbability (deterministicTypes c) τ (sigP h) j).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun j _ => hfin j), hs]; simp
  have h2 : ∑ j, (Pi_ c L j).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun j _ => hPfin j), hP]; simp
  have h3 : ∑ j, ((winProbability (deterministicTypes c) τ (sigP h) j).toReal - (Pi_ c L j).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, h1, h2]; simp
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2
    (ENNReal.toReal_mono (hfin j) (hge j)))).1 h3 i (Finset.mem_univ i)
  have h5 : (winProbability (deterministicTypes c) τ (sigP h) i).toReal = (Pi_ c L i).toReal := by
    linarith
  exact (ENNReal.toReal_eq_toReal_iff' (hfin i) (hPfin i)).1 h5

lemma Qf_le_one (c : Fin (n + 1) → ℝ) (L x : ℝ) (hL : ∀ k, c k < L) (hx : L ≤ x) :
    Qf c L x ≤ 1 := by
  unfold Qf
  rw [Real.exp_le_one_iff]
  unfold Hf
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sum_nonpos
  intro k _
  have := Real.log_le_log (sub_pos.2 (hL k)) (by linarith : L - c k ≤ x - c k)
  linarith

lemma lint_tail (B L : ℝ) (hB : 0 ≤ B) (hL : B < L) :
    ∫⁻ x in Ioi L, ENNReal.ofReal (2 * B / (x - B) ^ 2) = ENNReal.ofReal (2 * B / (L - B)) := by
  have hderiv : ∀ x ∈ Ioi L, HasDerivAt (fun y : ℝ => -(2 * B) * (y - B)⁻¹) (2 * B / (x - B) ^ 2) x := by
    intro x hx
    have hx' : x - B ≠ 0 := by have : L < x := hx; linarith
    have := (((hasDerivAt_id x).sub_const B).inv hx').const_mul (-(2 * B))
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have hnn : ∀ x ∈ Ioi L, 0 ≤ 2 * B / (x - B) ^ 2 := fun x _ => by positivity
  have hcont : ContinuousWithinAt (fun y : ℝ => -(2 * B) * (y - B)⁻¹) (Ici L) L := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_const
    exact ContinuousAt.inv₀ (continuousAt_id.sub continuousAt_const) (by simp; linarith)
  have htend : Tendsto (fun y : ℝ => -(2 * B) * (y - B)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (y - B)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    simpa using h1.const_mul (-(2 * B))
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn htend
  have hI := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn htend
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)), hint]
  congr 1
  have : L - B ≠ 0 := by linarith
  field_simp
  ring

lemma Pi_le {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (i j : Fin (n + 1)) :
    Pi_ c L i ≤ Pi_ c L j + ENNReal.ofReal (2 * Bnd c / (L - Bnd c)) := by
  have hB := Bnd_nonneg c
  have hm : ∀ i : Fin (n + 1), Measurable (fun x : ℝ => ENNReal.ofReal (Qf c L x * kap c i x)) := by
    intro i
    apply ENNReal.measurable_ofReal.comp
    unfold Qf Hf kap Kf
    fun_prop
  unfold Pi_
  rw [← lint_tail (Bnd c) L hB h.Bnd_lt, ← lintegral_add_left (hm j)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  have hx' : L < x := hx
  have hBx : Bnd c < x := h.Bnd_lt.trans hx'
  have hk := kap_le c i j x hBx
  have hq := Qf_pos c L x
  have hq1 := Qf_le_one c L x h.lt hx'.le
  have he : 0 ≤ 2 * Bnd c / (x - Bnd c) ^ 2 := by positivity
  rw [← ENNReal.ofReal_add (mul_nonneg hq.le (kap_nonneg c h.hn j x (h.hL.trans hx'.le))) he]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma Pi_real_le {c : Fin (n + 1) → ℝ} {L : ℝ} (h : Good c L) (τ : TieRule n) (i j : Fin (n + 1)) :
    (winProbability (deterministicTypes c) τ (sigP h) i).toReal ≤
      (winProbability (deterministicTypes c) τ (sigP h) j).toReal + 2 * Bnd c / (L - Bnd c) := by
  have hB := Bnd_nonneg c
  have hs := sum_win h τ
  have hfin : ∀ j, winProbability (deterministicTypes c) τ (sigP h) j ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => winProbability (deterministicTypes c) τ (sigP h) j)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have hle := Pi_le h i j
  rw [← win_eq_Pi h τ i, ← win_eq_Pi h τ j] at hle
  have hpos : 0 ≤ 2 * Bnd c / (L - Bnd c) := by
    have := h.Bnd_lt; apply div_nonneg (by positivity); linarith
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin j, ENNReal.ofReal_ne_top⟩) hle
  rwa [ENNReal.toReal_add (hfin j) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpos] at this

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31C
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31A
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31B
open ProcurementPoA.DeterministicCap.Supplement.Dev.L31C
open ProcurementPoA.DeterministicCap

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.L31D

variable {n : ℕ}

noncomputable def Lk (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ := (2 * n + 1) * Bnd c + 1 + k

lemma good_Lk (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (k : ℕ) : Good c (Lk c k) :=
  ⟨hn, by unfold Lk; have : (0 : ℝ) ≤ k := by positivity
          linarith⟩

lemma near (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (τ : TieRule n) (k : ℕ) (i : Fin (n + 1)) :
    |(winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) i).toReal - 1 / ((n : ℝ) + 1)|
      ≤ 2 * Bnd c / (Lk c k - Bnd c) := by
  set h := good_Lk c hn k
  set p : Fin (n + 1) → ℝ := fun j => (winProbability (deterministicTypes c) τ (sigP h) j).toReal
  set e := 2 * Bnd c / (Lk c k - Bnd c)
  have hs : ∑ j, p j = 1 := by
    have := sum_win h τ
    have hfin : ∀ j, winProbability (deterministicTypes c) τ (sigP h) j ≠ ⊤ := by
      intro j
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← this]
      exact Finset.single_le_sum (f := fun j => winProbability (deterministicTypes c) τ (sigP h) j)
        (fun _ _ => zero_le) (Finset.mem_univ j)
    have h2 := congrArg ENNReal.toReal this
    rw [ENNReal.toReal_sum (fun j _ => hfin j)] at h2
    simpa using h2
  have hle : ∀ a b, p a ≤ p b + e := fun a b => Pi_real_le h τ a b
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcard : ∑ _j : Fin (n + 1), (1 : ℝ) = (n : ℝ) + 1 := by simp
  have up : (n + 1 : ℝ) * p i ≤ 1 + (n + 1) * e := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle i j)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hs] at this
    push_cast at this
    linarith
  have lo : 1 ≤ (n + 1 : ℝ) * p i + (n + 1) * e := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hs] at this
    push_cast at this
    linarith
  have hq : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
  rw [abs_le]
  constructor
  · have a1 : ((n : ℝ) + 1) * (-e) ≤ ((n : ℝ) + 1) * (p i - 1 / ((n : ℝ) + 1)) := by
      nlinarith [lo, hq]
    exact le_of_mul_le_mul_left a1 hN
  · have a1 : ((n : ℝ) + 1) * (p i - 1 / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * e := by
      nlinarith [up, hq]
    exact le_of_mul_le_mul_left a1 hN


lemma sc_close (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (τ : TieRule n) (k : ℕ) :
    |deterministicSocialCost c τ (sigP (good_Lk c hn k)) - (∑ i, c i) / ((n + 1 : ℕ) : ℝ)|
      ≤ Bnd c * (2 * Bnd c / (Lk c k - Bnd c)) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e1 : (∑ i, c i) / ((n + 1 : ℕ) : ℝ) = ∑ i, c i * (1 / ((n : ℝ) + 1)) := by
    push_cast
    rw [← Finset.sum_mul]; ring
  have e2 : deterministicSocialCost c τ (sigP (good_Lk c hn k)) - (∑ i, c i) / ((n + 1 : ℕ) : ℝ)
      = ∑ i, c i * ((winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) i).toReal
          - 1 / ((n : ℝ) + 1)) := by
    rw [e1]
    unfold deterministicSocialCost
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i; ring
  rw [e2]
  calc |∑ i, c i * ((winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) i).toReal
          - 1 / ((n : ℝ) + 1))|
      ≤ ∑ i, |c i * ((winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) i).toReal
          - 1 / ((n : ℝ) + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (2 * Bnd c / (Lk c k - Bnd c)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (near c hn τ k i) (abs_nonneg _)
    _ = Bnd c * (2 * Bnd c / (Lk c k - Bnd c)) := by
        rw [← Finset.sum_mul]; rfl

lemma tendsto_sc (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (τ : TieRule n) :
    Tendsto (fun k => deterministicSocialCost c τ (sigP (good_Lk c hn k))) atTop
      (𝓝 ((∑ i, c i) / ((n + 1 : ℕ) : ℝ))) := by
  have hB := Bnd_nonneg c
  have he : Tendsto (fun k : ℕ => Bnd c * (2 * Bnd c / (Lk c k - Bnd c))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Lk c k - Bnd c) atTop atTop := by
      have : Tendsto (fun k : ℕ => (k : ℝ) + ((2 * n + 1) * Bnd c + 1 - Bnd c)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      refine this.congr (fun k => ?_)
      unfold Lk; ring
    have h2 : Tendsto (fun k : ℕ => 2 * Bnd c / (Lk c k - Bnd c)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using h2.const_mul (Bnd c)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) he
  rw [Real.norm_eq_abs]
  exact sc_close c hn τ k


lemma ae_cost_mem {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) :
    ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).1 ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
  have h1 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i), y.1 ∈ D.types i := by
    have h2 : ∀ᵐ y ∂(D.law i ⊗ₘ σ.bid i).fst, y ∈ D.types i := by
      rw [Measure.fst_compProd]
      exact mem_ae_iff.2 (D.concentrated i)
    exact ae_of_ae_map measurable_fst.aemeasurable h2
  exact hq.ae h1

lemma ae_type_mem {n : ℕ} (D : IndependentTypes n) :
    ∀ᵐ c ∂(typeLaw D), ∀ i, c i ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
  exact hq.ae (mem_ae_iff.2 (D.concentrated i))

lemma optimal_eq (c : Fin (n + 1) → ℝ) :
    optimalSocialCost (deterministicTypes c) = ENNReal.ofReal (lowest c) := by
  haveI : IsProbabilityMeasure (typeLaw (deterministicTypes c)) := by
    unfold typeLaw; infer_instance
  unfold optimalSocialCost
  have : ∀ᵐ x ∂(typeLaw (deterministicTypes c)), ENNReal.ofReal (lowest x) = ENNReal.ofReal (lowest c) := by
    filter_upwards [ae_type_mem (deterministicTypes c)] with x hx
    have : x = c := funext fun i => by simpa [deterministicTypes] using hx i
    rw [this]
  rw [lintegral_congr_ae this]
  simp

lemma sc_eq (c : Fin (n + 1) → ℝ) (hc : ∀ i, 0 ≤ c i) (τ : TieRule n) (σ : MixedProfile n) :
    standardSocialCost (deterministicTypes c) τ σ =
      ∑ i, ENNReal.ofReal (c i) * winProbability (deterministicTypes c) τ σ i := by
  have hg : Measurable (fun (x : Suppliers n → ℝ × ℝ) j => (x j).2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_pi_apply j))
  unfold standardSocialCost winnerCost winProbability
  have : ∀ᵐ x ∂(playLaw (deterministicTypes c) σ),
      ∑ i, ENNReal.ofReal (x i).1 * τ.select (fun j => (x j).2) {i} =
      ∑ i, ENNReal.ofReal (c i) * τ.select (fun j => (x j).2) {i} := by
    filter_upwards [ae_cost_mem (deterministicTypes c) σ] with x hx
    apply Finset.sum_congr rfl
    intro i _
    have : (x i).1 = c i := by simpa [deterministicTypes] using hx i
    rw [this]
  rw [lintegral_congr_ae this, lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    have hm : Measurable (fun x : Suppliers n → ℝ × ℝ => τ.select (fun j => (x j).2) {i}) :=
      (Kernel.measurable_coe τ.select (measurableSet_singleton i)).comp hg
    exact lintegral_const_mul _ hm
  · intro i _
    have hm : Measurable (fun x : Suppliers n → ℝ × ℝ => τ.select (fun j => (x j).2) {i}) :=
      (Kernel.measurable_coe τ.select (measurableSet_singleton i)).comp hg
    exact hm.const_mul _

lemma sc_eq_real (c : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (hc : ∀ i, 0 ≤ c i) (τ : TieRule n) (k : ℕ) :
    standardSocialCost (deterministicTypes c) τ (sigP (good_Lk c hn k)) =
      ENNReal.ofReal (deterministicSocialCost c τ (sigP (good_Lk c hn k))) := by
  rw [sc_eq c hc]
  unfold deterministicSocialCost
  have hs := sum_win (good_Lk c hn k) τ
  have hfin : ∀ j, winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) j ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hs]
    exact Finset.single_le_sum (f := fun j => winProbability (deterministicTypes c) τ (sigP (good_Lk c hn k)) j)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hc i) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (hc i), ENNReal.ofReal_toReal (hfin i)]

end ProcurementPoA.DeterministicCap.Supplement.Dev.L31D

namespace ProcurementPoA.DeterministicCap.Supplement

open Dev.L31D Dev.L31C in
theorem chk_lemma_3_1 {n : ℕ} (hn : 1 ≤ n) (c : Suppliers n → ℝ) (τ : TieRule n) :
    (∃ σ : ℕ → MixedProfile n,
      (∀ k, IsStandardBNE (deterministicTypes c) τ (σ k)) ∧
      Tendsto (fun k => deterministicSocialCost c τ (σ k)) atTop
        (𝓝 ((∑ i, c i) / (n + 1 : ℕ)))) ∧
    (0 < lowest c → ENNReal.ofReal (((∑ i, c i) / (n + 1 : ℕ)) / lowest c) ≤
      standardInstancePoA (deterministicTypes c) τ) := by
  refine ⟨⟨fun k => sigP (good_Lk c hn k), fun k => isBNE (good_Lk c hn k) τ, tendsto_sc c hn τ⟩, ?_⟩
  intro hlow
  have hc : ∀ i, 0 ≤ c i := fun i => by
    have : lowest c ≤ c i := by unfold lowest; exact Finset.inf'_le _ (Finset.mem_univ i)
    linarith
  have hq : Tendsto (fun k => standardSocialCost (deterministicTypes c) τ (sigP (good_Lk c hn k)) /
      optimalSocialCost (deterministicTypes c)) atTop
      (𝓝 (ENNReal.ofReal (((∑ i, c i) / ((n + 1 : ℕ) : ℝ)) / lowest c))) := by
    have h1 := ((tendsto_sc c hn τ).div_const (lowest c))
    have h2 := ENNReal.tendsto_ofReal h1
    refine h2.congr (fun k => ?_)
    rw [sc_eq_real c hn hc τ k, optimal_eq, ENNReal.ofReal_div_of_pos hlow]
  refine le_of_tendsto' hq (fun k => ?_)
  unfold standardInstancePoA
  exact le_sSup ⟨sigP (good_Lk c hn k), isBNE (good_Lk c hn k) τ, rfl⟩

end ProcurementPoA.DeterministicCap.Supplement
end

theorem solution : type_of% @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_3_1 := @ProcurementPoA.DeterministicCap.Supplement.chk_lemma_3_1
