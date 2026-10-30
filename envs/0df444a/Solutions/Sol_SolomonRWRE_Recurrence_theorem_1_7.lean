-- Prove2me | solution 1 for SolomonRWRE.Recurrence.theorem_1_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T06:28:55.692993+00:00
-- url     : https://prove2.me/submissions/710d47d9-6b46-4c6f-8929-5d47bd0e4a3f

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model
import Theorems.Thm_SolomonRWRE_Recurrence_theorem_0_1
import Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_5
import Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_6
import Theorems.Thm_SolomonRWRE_Recurrence_proof_1_7_boundary
import Theorems.Thm_SolomonRWRE_Recurrence_proof_1_7_log_moment

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RWREGlue
open SolomonRWRE.Recurrence

/-- The real log-ratio `ln((1 - t)/t)`. -/
noncomputable def L (t : ℝ) : ℝ := Real.log ((1 - t) / t)

/-- `σ` as a function of the single site value. -/
noncomputable def sfun (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 - t) / ENNReal.ofReal t

lemma measurable_L : Measurable L := by
  unfold L; fun_prop

lemma measurable_sfun : Measurable sfun := by
  unfold sfun
  exact (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)).div
    ENNReal.measurable_ofReal

lemma sigma_eq_sfun (a : ℤ → ℝ) (k : ℤ) : sigma a k = sfun (a k) := rfl

lemma sfun_interior {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    sfun t = ENNReal.ofReal (Real.exp (L t)) := by
  unfold sfun L
  rw [Real.exp_log (div_pos (by linarith) h0), ENNReal.ofReal_div_of_pos h0]

lemma prod_Icc_pos {M : Type*} [CommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∏ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), f k =
      ∏ j ∈ Finset.range (n + 1), f ((j : ℤ) + 1) := by
  symm
  apply Finset.prod_nbij' (fun j : ℕ => (j : ℤ) + 1) (fun k : ℤ => (k - 1).toNat)
  · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro j _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j _; rfl

lemma prod_Icc_neg {M : Type*} [CommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∏ k ∈ Finset.Icc (-((n : ℤ) + 1)) (-1), f k =
      ∏ j ∈ Finset.range (n + 1), f (-((j : ℤ) + 1)) := by
  symm
  apply Finset.prod_nbij' (fun j : ℕ => -((j : ℤ) + 1)) (fun k : ℤ => (-k - 1).toNat)
  · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro j _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j _; rfl

lemma rho_pos (a : ℤ → ℝ) (n : ℕ) :
    rho a ((n : ℤ) + 1) = ∏ j ∈ Finset.range (n + 1), sfun (a ((j : ℤ) + 1)) := by
  unfold rho
  rw [if_pos (by omega)]
  exact prod_Icc_pos (fun k => sigma a k) n

lemma rho_neg (a : ℤ → ℝ) (n : ℕ) :
    rho a (-((n : ℤ) + 1)) = ∏ j ∈ Finset.range (n + 1), sfun (a (-((j : ℤ) + 1))) := by
  unfold rho
  rw [if_neg (by omega)]
  exact prod_Icc_neg (fun k => sigma a k) n

lemma prod_ofReal_exp (s : Finset ℕ) (x : ℕ → ℝ) :
    ∏ j ∈ s, ENNReal.ofReal (Real.exp (x j)) = ENNReal.ofReal (Real.exp (∑ j ∈ s, x j)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]

/-- All sites are interior. -/
def Interior (a : ℤ → ℝ) : Prop := ∀ n, 0 < a n ∧ a n < 1

lemma rho_pos_interior {a : ℤ → ℝ} (ha : Interior a) (n : ℕ) :
    rho a ((n : ℤ) + 1) =
      ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range (n + 1), L (a ((j : ℤ) + 1)))) := by
  rw [rho_pos, ← prod_ofReal_exp]
  exact Finset.prod_congr rfl fun j _ => sfun_interior (ha _).1 (ha _).2

lemma rho_neg_inv_interior {a : ℤ → ℝ} (ha : Interior a) (n : ℕ) :
    (rho a (-((n : ℤ) + 1)))⁻¹ =
      ENNReal.ofReal (Real.exp (-∑ j ∈ Finset.range (n + 1), L (a (-((j : ℤ) + 1))))) := by
  rw [rho_neg]
  have : ∏ j ∈ Finset.range (n + 1), sfun (a (-((j : ℤ) + 1))) =
      ENNReal.ofReal (Real.exp (∑ j ∈ Finset.range (n + 1), L (a (-((j : ℤ) + 1))))) := by
    rw [← prod_ofReal_exp]
    exact Finset.prod_congr rfl fun j _ => sfun_interior (ha _).1 (ha _).2
  rw [this, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℤ → Ω → ℝ} {X : ℕ → Ω → ℤ}

lemma map_vec (hRW : IsRWRE P α X) {m : ℕ} (g : Fin m → ℤ) (hg : g.Injective) :
    P.map (fun ω (j : Fin m) => α (g j) ω) = Measure.pi (fun _ : Fin m => P.map (α 0)) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := P) (f := fun j : Fin m => α (g j))
    (fun j => (hRW.meas_α (g j)).aemeasurable)).mp (hRW.indep.precomp hg)
  rw [h]
  congr 1
  funext j
  exact (hRW.ident (g j)).map_eq

lemma prob_vec_eq (hRW : IsRWRE P α X) {m : ℕ} (g₁ g₂ : Fin m → ℤ) (h₁ : g₁.Injective)
    (h₂ : g₂.Injective) {B : Set (Fin m → ℝ)} (hB : MeasurableSet B) :
    P {ω | (fun j => α (g₁ j) ω) ∈ B} = P {ω | (fun j => α (g₂ j) ω) ∈ B} := by
  have m₁ : Measurable (fun ω (j : Fin m) => α (g₁ j) ω) :=
    measurable_pi_lambda _ fun j => hRW.meas_α _
  have m₂ : Measurable (fun ω (j : Fin m) => α (g₂ j) ω) :=
    measurable_pi_lambda _ fun j => hRW.meas_α _
  have e₁ : P {ω | (fun j => α (g₁ j) ω) ∈ B} = P.map (fun ω (j : Fin m) => α (g₁ j) ω) B :=
    (Measure.map_apply m₁ hB).symm
  have e₂ : P {ω | (fun j => α (g₂ j) ω) ∈ B} = P.map (fun ω (j : Fin m) => α (g₂ j) ω) B :=
    (Measure.map_apply m₂ hB).symm
  rw [e₁, e₂, map_vec hRW g₁ h₁, map_vec hRW g₂ h₂]

lemma ident_eq (hRW : IsRWRE P α X) (n : ℤ) (t : ℝ) :
    P {ω | α n ω = t} = P {ω | α 0 ω = t} :=
  (hRW.ident n).measure_mem_eq (measurableSet_singleton t)

lemma ae_interior (hRW : IsRWRE P α X) (h0 : P {ω | α 0 ω = 0} = 0)
    (h1 : P {ω | α 0 ω = 1} = 0) : ∀ᵐ ω ∂P, Interior (env α ω) := by
  refine ae_all_iff.mpr fun n => ?_
  have a0 : ∀ᵐ ω ∂P, α n ω ≠ 0 := by
    rw [ae_iff]; simpa [ident_eq hRW n] using h0
  have a1 : ∀ᵐ ω ∂P, α n ω ≠ 1 := by
    rw [ae_iff]; simpa [ident_eq hRW n] using h1
  filter_upwards [a0, a1] with ω h0' h1'
  have := hRW.mem n ω
  simp only [Set.mem_Icc] at this
  exact ⟨lt_of_le_of_ne this.1 (Ne.symm h0'), lt_of_le_of_ne this.2 h1'⟩

/-- `L(α_{g j})`. -/
noncomputable def Yp (α : ℤ → Ω → ℝ) (g : ℕ → ℤ) : ℕ → Ω → ℝ := fun j ω => L (α (g j) ω)
/-- `-L(α_{g j})`. -/
noncomputable def Yn (α : ℤ → Ω → ℝ) (g : ℕ → ℤ) : ℕ → Ω → ℝ := fun j ω => -L (α (g j) ω)

lemma partialSum_Yn (g : ℕ → ℤ) (n : ℕ) (ω : Ω) :
    partialSum (Yn α g) n ω = -partialSum (Yp α g) n ω := by
  unfold partialSum Yn Yp; rw [Finset.sum_neg_distrib]

lemma Yp_meas (hRW : IsRWRE P α X) (g : ℕ → ℤ) (j : ℕ) : Measurable (Yp α g j) :=
  measurable_L.comp (hRW.meas_α _)

lemma Yn_meas (hRW : IsRWRE P α X) (g : ℕ → ℤ) (j : ℕ) : Measurable (Yn α g j) :=
  (measurable_L.comp (hRW.meas_α _)).neg

lemma Yp_indep (hRW : IsRWRE P α X) {g : ℕ → ℤ} (hg : g.Injective) : iIndepFun (Yp α g) P :=
  (hRW.indep.precomp hg).comp (fun _ t => L t) (fun _ => measurable_L)

lemma Yn_indep (hRW : IsRWRE P α X) {g : ℕ → ℤ} (hg : g.Injective) : iIndepFun (Yn α g) P :=
  (hRW.indep.precomp hg).comp (fun _ t => -L t) (fun _ => measurable_L.neg)

lemma Yp_ident (hRW : IsRWRE P α X) (g : ℕ → ℤ) (j : ℕ) :
    IdentDistrib (Yp α g j) (Yp α g 0) P P :=
  ((hRW.ident (g j)).trans (hRW.ident (g 0)).symm).comp measurable_L

lemma Yn_ident (hRW : IsRWRE P α X) (g : ℕ → ℤ) (j : ℕ) :
    IdentDistrib (Yn α g j) (Yn α g 0) P P :=
  ((hRW.ident (g j)).trans (hRW.ident (g 0)).symm).comp measurable_L.neg

lemma L_inj {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (d : ℝ) (h : L t = d) :
    t = 1 / (1 + Real.exp d) := by
  unfold L at h
  have hx : (1 - t) / t = Real.exp d := by
    rw [← h, Real.exp_log (div_pos (by linarith) h0)]
  have ht : t ≠ 0 := h0.ne'
  rw [div_eq_iff ht] at hx
  have : 1 + Real.exp d ≠ 0 := by positivity
  field_simp
  linarith

lemma Yp_nd (hRW : IsRWRE P α X) (hint : ∀ᵐ ω ∂P, Interior (env α ω))
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c) (g : ℕ → ℤ) :
    ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Yp α g 0 ω = c := by
  rintro ⟨d, hd⟩
  apply hnd
  refine ⟨1 / (1 + Real.exp d), ?_⟩
  have hg : ∀ᵐ ω ∂P, α (g 0) ω = 1 / (1 + Real.exp d) := by
    filter_upwards [hint, hd] with ω hi hω
    exact L_inj (hi (g 0)).1 (hi (g 0)).2 d hω
  have e := (hRW.ident (g 0)).measure_mem_eq (measurableSet_singleton (1 / (1 + Real.exp d))).compl
  rw [ae_iff] at hg ⊢
  have e' : P {ω | ¬ α (g 0) ω = 1 / (1 + Real.exp d)} =
      P {ω | ¬ α 0 ω = 1 / (1 + Real.exp d)} := e
  rw [← e']; exact hg

lemma Yn_nd (hRW : IsRWRE P α X) (hint : ∀ᵐ ω ∂P, Interior (env α ω))
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c) (g : ℕ → ℤ) :
    ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Yn α g 0 ω = c := by
  rintro ⟨d, hd⟩
  apply Yp_nd hRW hint hnd g
  refine ⟨-d, ?_⟩
  filter_upwards [hd] with ω hω
  unfold Yn at hω; unfold Yp; linarith

end Prob

section Series
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℤ → Ω → ℝ} {X : ℕ → Ω → ℤ}

/-- Spitzer series `Σ n⁻¹ P(S_n > 0)`. -/
noncomputable def G (P : Measure Ω) (Y : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < partialSum Y (n + 1) ω}

/-- Spitzer series `Σ n⁻¹ P(S_n < 0)`. -/
noncomputable def Ls (P : Measure Ω) (Y : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | partialSum Y (n + 1) ω < 0}

/-- forward index `j ↦ j + 1`. -/
def fw : ℕ → ℤ := fun j => (j : ℤ) + 1
/-- backward index `j ↦ -(j + 1)`. -/
def bw : ℕ → ℤ := fun j => -((j : ℤ) + 1)

lemma fw_inj : fw.Injective := fun a b h => by unfold fw at h; omega
lemma bw_inj : bw.Injective := fun a b h => by unfold bw at h; omega

lemma Ls_eq_G_Yn (g : ℕ → ℤ) : Ls P (Yp α g) = G P (Yn α g) := by
  unfold Ls G
  congr 1; funext n; congr 2; ext ω
  simp only [Set.mem_setOf_eq, partialSum_Yn, neg_pos]

lemma partialSum_Yp (g : ℕ → ℤ) (n : ℕ) (ω : Ω) :
    partialSum (Yp α g) (n + 1) ω = ∑ j : Fin (n + 1), L (α (g j) ω) := by
  unfold partialSum Yp; rw [Finset.sum_range]

lemma G_bw (hRW : IsRWRE P α X) : G P (Yp α bw) = G P (Yp α fw) := by
  unfold G
  congr 1; funext n; congr 1
  simp only [partialSum_Yp]
  have hB : MeasurableSet {v : Fin (n + 1) → ℝ | 0 < ∑ j, L (v j)} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun j _ => measurable_L.comp (measurable_pi_apply j))
  exact prob_vec_eq hRW (fun j : Fin (n + 1) => bw j) (fun j => fw j)
    (fun a b h => Fin.ext (bw_inj h)) (fun a b h => Fin.ext (fw_inj h)) hB

lemma Ls_bw (hRW : IsRWRE P α X) : Ls P (Yp α bw) = Ls P (Yp α fw) := by
  unfold Ls
  congr 1; funext n; congr 1
  simp only [partialSum_Yp]
  have hB : MeasurableSet {v : Fin (n + 1) → ℝ | ∑ j, L (v j) < 0} :=
    measurableSet_lt
      (Finset.measurable_sum _ fun j _ => measurable_L.comp (measurable_pi_apply j))
      measurable_const
  exact prob_vec_eq hRW (fun j : Fin (n + 1) => bw j) (fun j => fw j)
    (fun a b h => Fin.ext (bw_inj h)) (fun a b h => Fin.ext (fw_inj h)) hB

lemma rho_fw (ω : Ω) (hω : Interior (env α ω)) (n : ℕ) :
    rho (env α ω) ((n : ℤ) + 1) = ENNReal.ofReal (Real.exp (partialSum (Yp α fw) (n + 1) ω)) := by
  rw [rho_pos_interior hω]; rfl

lemma rho_bw (ω : Ω) (hω : Interior (env α ω)) (n : ℕ) :
    (rho (env α ω) (-((n : ℤ) + 1)))⁻¹ =
      ENNReal.ofReal (Real.exp (-partialSum (Yp α bw) (n + 1) ω)) := by
  rw [rho_neg_inv_interior hω]; rfl

lemma seriesGt_eq (hint : ∀ᵐ ω ∂P, Interior (env α ω)) : seriesGt P α = G P (Yp α fw) := by
  unfold seriesGt G
  congr 1; funext n; congr 1
  refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
  filter_upwards [hint] with ω hω
  simp only [Set.mem_setOf_eq, rho_fw ω hω, ENNReal.one_lt_ofReal]
  have h := @Real.exp_lt_exp 0 (partialSum (Yp α fw) (n + 1) ω)
  rw [Real.exp_zero] at h; exact h

lemma seriesLt_eq (hint : ∀ᵐ ω ∂P, Interior (env α ω)) : seriesLt P α = Ls P (Yp α fw) := by
  unfold seriesLt Ls
  congr 1; funext n; congr 1
  refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
  filter_upwards [hint] with ω hω
  simp only [Set.mem_setOf_eq, rho_fw ω hω, ENNReal.ofReal_lt_one]
  have h := @Real.exp_lt_exp (partialSum (Yp α fw) (n + 1) ω) 0
  rw [Real.exp_zero] at h; exact h

lemma tsum_exp_top {s : ℕ → ℝ} (h : Tendsto s atTop atTop) :
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (s (n + 1))) = ∞ := by
  by_contra hne
  have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
  have e1 := h0.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
  have e2 := (h.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop (0 : ℝ))
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (s (n + 1))) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hn2)
  exact absurd hn1 (not_lt.mpr this)

lemma measurable_env (hRW : IsRWRE P α X) : Measurable (env α) :=
  measurable_pi_lambda _ hRW.meas_α

lemma measurable_rho (k : ℤ) : Measurable fun a : ℤ → ℝ => rho a k := by
  unfold rho
  split_ifs
  · exact Finset.measurable_prod _ fun i _ => measurable_sfun.comp (measurable_pi_apply i)
  · exact Finset.measurable_prod _ fun i _ => measurable_sfun.comp (measurable_pi_apply i)

lemma measurableSet_interior : MeasurableSet {a : ℤ → ℝ | Interior a} := by
  have : {a : ℤ → ℝ | Interior a} = ⋂ n, ({a | 0 < a n} ∩ {a | a n < 1}) := by
    ext a; simp [Interior]
  rw [this]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_lt measurable_const (measurable_pi_apply n)).inter
      (measurableSet_lt (measurable_pi_apply n) measurable_const)

lemma meas_sumPos : Measurable fun a : ℤ → ℝ => ∑' n : ℕ, rho a ((n : ℤ) + 1) :=
  Measurable.ennreal_tsum fun n => measurable_rho _

lemma meas_sumNeg : Measurable fun a : ℤ → ℝ => ∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ :=
  Measurable.ennreal_tsum fun n => (measurable_rho _).inv

lemma measurableSet_top : MeasurableSet {w : ℕ → ℤ | Tendsto w atTop atTop} := by
  have : {w : ℕ → ℤ | Tendsto w atTop atTop} =
      ⋂ M : ℤ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {w | M ≤ w n} := by
    ext w; simp [tendsto_atTop, eventually_atTop]
  rw [this]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply n)

lemma measurableSet_bot : MeasurableSet {w : ℕ → ℤ | Tendsto w atTop atBot} := by
  have : {w : ℕ → ℤ | Tendsto w atTop atBot} =
      ⋂ M : ℤ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), {w | w n ≤ M} := by
    ext w; simp [tendsto_atBot, eventually_atTop]
  rw [this]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply n) measurable_const

lemma measurableSet_osc : MeasurableSet {w : ℕ → ℤ | Oscillates w} := by
  have : {w : ℕ → ℤ | Oscillates w} =
      (⋂ M : ℤ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {w | w n ≤ M}) ∩
      (⋂ M : ℤ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {w | M ≤ w n}) := by
    ext w; simp [Oscillates, frequently_atTop]
  rw [this]
  exact (MeasurableSet.iInter fun M => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => measurableSet_le (measurable_pi_apply n) measurable_const).inter
    (MeasurableSet.iInter fun M => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun _ => measurableSet_le measurable_const (measurable_pi_apply n))

/-- Transfer a quenched a.s. statement to the annealed walk via `theorem_0_1`. -/
lemma annealed (hRW : IsRWRE P α X) (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (E : Set (ℤ → ℝ)) (hE : MeasurableSet E) (hPE : ∀ᵐ ω ∂P, env α ω ∈ E)
    (hq : ∀ a ∈ E, ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ∀ᵐ w ∂ν, w ∈ S) :
    ∀ᵐ ω ∂P, (fun n => X n ω) ∈ S := by
  have hQ : ∀ᵐ a ∂(P.map (env α)), a ∈ E :=
    (ae_map_iff (measurable_env hRW).aemeasurable (p := fun a => a ∈ E) hE).mpr hPE
  have h1 := theorem_0_1 P α X hRW S hS (by
    filter_upwards [hQ] with ω hω
    intro ν hν hc
    have := hq _ hω ν hν hc
    rw [ae_iff] at this
    exact (prob_compl_eq_zero_iff hS).mp this)
  have hm : MeasurableSet {ω | (fun n => X n ω) ∈ S} :=
    (measurable_pi_lambda _ hRW.meas_X) hS
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff hm).mpr h1

end Series

section Main
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℤ → Ω → ℝ} {X : ℕ → Ω → ℤ}

lemma interior_case (hRW : IsRWRE P α X) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hint : ∀ᵐ ω ∂P, Interior (env α ω)) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by
  have L6pf := lemma_1_6 P (Yp α fw) (Yp_meas hRW fw) (Yp_indep hRW fw_inj) (Yp_ident hRW fw)
    (Yp_nd hRW hint hnd fw)
  have L6pb := lemma_1_6 P (Yp α bw) (Yp_meas hRW bw) (Yp_indep hRW bw_inj) (Yp_ident hRW bw)
    (Yp_nd hRW hint hnd bw)
  have L6nf := lemma_1_6 P (Yn α fw) (Yn_meas hRW fw) (Yn_indep hRW fw_inj) (Yn_ident hRW fw)
    (Yn_nd hRW hint hnd fw)
  have L6nb := lemma_1_6 P (Yn α bw) (Yn_meas hRW bw) (Yn_indep hRW bw_inj) (Yn_ident hRW bw)
    (Yn_nd hRW hint hnd bw)
  have hGt : seriesGt P α = G P (Yp α fw) := seriesGt_eq hint
  have hLt : seriesLt P α = Ls P (Yp α fw) := seriesLt_eq hint
  have hGb : G P (Yp α bw) = G P (Yp α fw) := G_bw hRW
  have hLb : Ls P (Yp α bw) = Ls P (Yp α fw) := Ls_bw hRW
  have mI := measurableSet_interior
  have mN := meas_sumNeg (measurableSet_singleton ∞)
  have mP := meas_sumPos (measurableSet_singleton ∞)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hG : G P (Yp α fw) ≠ ∞ := by rw [← hGt]; exact h
    have t1 : ∀ᵐ ω ∂P, Tendsto (fun n => partialSum (Yp α fw) n ω) atTop atBot := L6pf.1.1.1 hG
    have s1 := L6pf.1.2 t1
    have hG' : G P (Yp α bw) ≠ ∞ := by rw [hGb]; exact hG
    have t2 : ∀ᵐ ω ∂P, Tendsto (fun n => partialSum (Yp α bw) n ω) atTop atBot := L6pb.1.1.1 hG'
    refine annealed hRW _ measurableSet_top
      {a | Interior a ∧ ∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ ∧
        ∑' n : ℕ, rho a ((n : ℤ) + 1) ≠ ∞} (mI.inter (mN.inter mP.compl)) ?_ ?_
    · filter_upwards [hint, s1, t2] with ω hi hs ht
      refine ⟨hi, ?_, ?_⟩
      · simp_rw [rho_bw ω hi]
        exact tsum_exp_top (s := fun n => -partialSum (Yp α bw) n ω)
          (tendsto_neg_atBot_atTop.comp ht)
      · simp_rw [rho_fw ω hi]; exact hs
    · rintro a ⟨ha, h1, h2⟩ ν hν hc
      exact (lemma_1_5 ν a ha (fun n w => w n) hc).1 h1 h2
  · have hG : G P (Yn α fw) ≠ ∞ := by rw [← Ls_eq_G_Yn, ← hLt]; exact h
    have t1 : ∀ᵐ ω ∂P, Tendsto (fun n => partialSum (Yn α fw) n ω) atTop atBot := L6nf.1.1.1 hG
    have hG' : G P (Yn α bw) ≠ ∞ := by rw [← Ls_eq_G_Yn, hLb, ← hLt]; exact h
    have t2 : ∀ᵐ ω ∂P, Tendsto (fun n => partialSum (Yn α bw) n ω) atTop atBot := L6nb.1.1.1 hG'
    have s2 := L6nb.1.2 t2
    refine annealed hRW _ measurableSet_bot
      {a | Interior a ∧ ∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ ≠ ∞ ∧
        ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞} (mI.inter (mN.compl.inter mP)) ?_ ?_
    · filter_upwards [hint, s2, t1] with ω hi hs ht
      refine ⟨hi, ?_, ?_⟩
      · simp_rw [rho_bw ω hi, ← partialSum_Yn]; exact hs
      · simp_rw [rho_fw ω hi]
        have e : (fun n => partialSum (Yp α fw) n ω) = fun n => -partialSum (Yn α fw) n ω := by
          funext n; rw [partialSum_Yn, neg_neg]
        exact tsum_exp_top (s := fun n => partialSum (Yp α fw) n ω)
          (e ▸ tendsto_neg_atBot_atTop.comp ht)
    · rintro a ⟨ha, h1, h2⟩ ν hν hc
      exact (lemma_1_5 ν a ha (fun n w => w n) hc).2.1 h1 h2
  · have hf : G P (Yp α fw) = ∞ ∧ Ls P (Yp α fw) = ∞ := by
      rw [← hGt, ← hLt]; exact ⟨h.2, h.1⟩
    have hb : G P (Yp α bw) = ∞ ∧ Ls P (Yp α bw) = ∞ := by rw [hGb, hLb]; exact hf
    have sf := L6pf.2.2 (L6pf.2.1.mp hf)
    have sb := L6pb.2.2 (L6pb.2.1.mp hb)
    refine annealed hRW _ measurableSet_osc
      {a | Interior a ∧ ∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ ∧
        ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞} (mI.inter (mN.inter mP)) ?_ ?_
    · filter_upwards [hint, sf, sb] with ω hi hsf hsb
      refine ⟨hi, ?_, ?_⟩
      · simp_rw [rho_bw ω hi]; exact hsb.1
      · simp_rw [rho_fw ω hi]; exact hsf.2
    · rintro a ⟨ha, h1, h2⟩ ν hν hc
      exact (lemma_1_5 ν a ha (fun n w => w n) hc).2.2 h1 h2

lemma harmonic_top {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0) (hu : ∀ n, c ≤ u n) :
    ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * u n = ∞ := by
  have hh : ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ = ∞ := by
    by_contra hne
    have hs := ENNReal.summable_toReal hne
    have : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
      refine hs.congr fun n => ?_
      rw [ENNReal.toReal_inv, show ((n : ℝ≥0∞) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) by push_cast; rfl,
        ENNReal.toReal_natCast, one_div]
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ)) 1).mp this)
  refine eq_top_mono (ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl (hu n)) ?_
  rw [ENNReal.tsum_mul_right, hh, ENNReal.top_mul hc]

lemma sfun_ne_zero {t : ℝ} (ht : t < 1) : sfun t ≠ 0 := by
  unfold sfun
  rw [Ne, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨(ENNReal.ofReal_pos.mpr (by linarith)).ne', ENNReal.ofReal_ne_top⟩

lemma sfun_ne_top {t : ℝ} (ht : 0 < t) : sfun t ≠ ∞ := by
  unfold sfun
  intro h
  rcases ENNReal.div_eq_top.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact (ENNReal.ofReal_pos.mpr ht).ne' h2
  · exact ENNReal.ofReal_ne_top h1

lemma case_one (hRW : IsRWRE P α X) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1))
    (hB1 : 0 < P {ω | α 0 ω = 1}) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by
  have hpos : ∀ n ω, 0 < α n ω := by
    rcases hrange with h | h
    · exfalso
      have : {ω | α 0 ω = 1} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact (h 0 ω).2.ne
      rw [this, measure_empty] at hB1; exact lt_irrefl _ hB1
    · exact fun n ω => (h n ω).1
  obtain ⟨hGt, hT⟩ := (proof_1_7_boundary P α X hRW hnd).1 ⟨hB1, hpos⟩
  have hLt : seriesLt P α = ∞ := by
    unfold seriesLt
    refine harmonic_top hB1.ne' fun n => ?_
    rw [← ident_eq hRW 1 1]
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [rho_pos, Finset.prod_eq_zero (i := 0) (by simp) (by simp [env, hω, sfun])]
    exact zero_lt_one
  exact ⟨fun _ => hT, fun h => absurd hLt h, fun h => absurd h.2 hGt⟩

lemma case_zero (hRW : IsRWRE P α X) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1))
    (hB0 : 0 < P {ω | α 0 ω = 0}) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by
  have hlt : ∀ n ω, α n ω < 1 := by
    rcases hrange with h | h
    · exact fun n ω => (h n ω).2
    · exfalso
      have : {ω | α 0 ω = 0} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact (h 0 ω).1.ne'
      rw [this, measure_empty] at hB0; exact lt_irrefl _ hB0
  obtain ⟨hLt, hB⟩ := (proof_1_7_boundary P α X hRW hnd).2 ⟨hB0, hlt⟩
  have hGt : seriesGt P α = ∞ := by
    unfold seriesGt
    refine harmonic_top hB0.ne' fun n => ?_
    rw [← ident_eq hRW 1 0]
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [rho_pos, Finset.prod_range_succ']
    have h0 : sfun (env α ω (((0 : ℕ) : ℤ) + 1)) = ∞ := by
      simp only [env, Nat.cast_zero, zero_add, hω, sfun, sub_zero, ENNReal.ofReal_one,
        ENNReal.ofReal_zero]
      exact ENNReal.div_zero one_ne_zero
    have hr : ∏ i ∈ Finset.range n, sfun (env α ω (((i + 1 : ℕ) : ℤ) + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => sfun_ne_zero (hlt _ ω)
    rw [h0, ENNReal.mul_top hr]
    exact ENNReal.one_lt_top
  exact ⟨fun h => absurd hGt h, fun _ => hB, fun h => absurd h.1 hLt⟩

lemma main3 (hRW : IsRWRE P α X) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1)) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by
  by_cases hB1 : 0 < P {ω | α 0 ω = 1}
  · exact case_one hRW hnd hrange hB1
  by_cases hB0 : 0 < P {ω | α 0 ω = 0}
  · exact case_zero hRW hnd hrange hB0
  rw [not_lt, nonpos_iff_eq_zero] at hB1 hB0
  exact interior_case hRW hnd (ae_interior hRW hB0 hB1)

end Main

section Refl
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℤ → Ω → ℝ} {X : ℕ → Ω → ℤ}

/-- The reflected environment `α'_n = 1 - α_{-n}`. -/
def refl (α : ℤ → Ω → ℝ) : ℤ → Ω → ℝ := fun n ω => 1 - α (-n) ω

lemma step_refl (a : ℤ → ℝ) (x y : ℤ) :
    step (fun m => 1 - a (-m)) x y = step a (-x) (-y) := by
  unfold step
  split_ifs <;> first | rfl | (exfalso; omega) | ring

lemma refl_RWRE (hRW : IsRWRE P α X) : IsRWRE P (refl α) (fun n ω => -X n ω) where
  meas_α n := measurable_const.sub (hRW.meas_α _)
  meas_X n := (hRW.meas_X n).neg
  mem n ω := by
    have := hRW.mem (-n) ω
    simp only [Set.mem_Icc] at this ⊢
    unfold refl; constructor <;> linarith
  indep := (hRW.indep.precomp neg_injective).comp (fun _ t => 1 - t)
    (fun _ => measurable_const.sub measurable_id)
  ident n := by
    have := (hRW.ident (-n)).comp (u := fun t : ℝ => 1 - t) (measurable_const.sub measurable_id)
    show IdentDistrib (fun ω => 1 - α (-n) ω) (fun ω => 1 - α (-0) ω) P P
    rw [neg_zero]; exact this
  law n x A hA := by
    have hR : Measurable (fun a : ℤ → ℝ => fun m : ℤ => 1 - a (-m)) :=
      measurable_pi_lambda _ fun m => measurable_const.sub (measurable_pi_apply _)
    have e1 : {ω | (fun m => refl α m ω) ∈ A} =
        {ω | (fun m => α m ω) ∈ (fun a : ℤ → ℝ => fun m : ℤ => 1 - a (-m)) ⁻¹' A} := rfl
    have e2 : {ω | ∀ k ≤ n, (fun n ω => -X n ω) k ω = x k} =
        {ω | ∀ k ≤ n, X k ω = (fun k => -x k) k} := by
      ext ω; simp only [Set.mem_setOf_eq]
      constructor <;> intro h k hk <;> have := h k hk <;> omega
    rw [e1, e2, hRW.law n (fun k => -x k) _ (hR hA)]
    congr 1
    funext ω
    have hp : ∏ k ∈ Finset.range n, step (fun m => α m ω) (-x k) (-x (k + 1)) =
        ∏ k ∈ Finset.range n, step (fun m => refl α m ω) (x k) (x (k + 1)) :=
      Finset.prod_congr rfl fun k _ => (step_refl (fun m => α m ω) (x k) (x (k + 1))).symm
    simp only [neg_eq_zero]
    rw [hp]

lemma sfun_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : sfun (1 - t) = (sfun t)⁻¹ := by
  unfold sfun
  rw [sub_sub_cancel, ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)]
  rcases h0.lt_or_eq with h | h
  · exact Or.inl (ENNReal.ofReal_pos.mpr h).ne'
  · exact Or.inr (ENNReal.ofReal_pos.mpr (by rw [← h]; norm_num)).ne'

lemma sigma_refl (hRW : IsRWRE P α X) (ω : Ω) (k : ℤ) :
    sigma (env (refl α) ω) k = (sigma (env α ω) (-k))⁻¹ := by
  rw [sigma_eq_sfun, sigma_eq_sfun]
  have := hRW.mem (-k) ω
  exact sfun_one_sub this.1 this.2

lemma logPos_refl (hRW : IsRWRE P α X) : logMomentPos P (refl α) = logMomentNeg P α := by
  unfold logMomentPos logMomentNeg logSigma
  congr 1; funext ω
  rw [sigma_refl hRW ω 0, neg_zero, ENNReal.log_inv]

lemma logNeg_refl (hRW : IsRWRE P α X) : logMomentNeg P (refl α) = logMomentPos P α := by
  unfold logMomentPos logMomentNeg logSigma
  congr 1; funext ω
  rw [sigma_refl hRW ω 0, neg_zero, ENNReal.log_inv, neg_neg]

lemma seriesGt_refl (hRW : IsRWRE P α X)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1)) :
    seriesGt P (refl α) = seriesLt P α := by
  unfold seriesGt seriesLt
  congr 1; funext n; congr 1
  have hpt : ∀ ω, rho (env (refl α) ω) ((n : ℤ) + 1) = (rho (env α ω) (-((n : ℤ) + 1)))⁻¹ := by
    intro ω
    rw [rho_pos, rho_neg]
    have e : ∀ j ∈ Finset.range (n + 1), sfun (env (refl α) ω ((j : ℤ) + 1)) =
        (sfun (env α ω (-((j : ℤ) + 1))))⁻¹ := fun j _ => sigma_refl hRW ω _
    rw [Finset.prod_congr rfl e, ENNReal.prod_inv_distrib]
    intro i _ j _ _
    rcases hrange with h | h
    · exact Or.inl (sfun_ne_zero (h _ ω).2)
    · exact Or.inr (sfun_ne_top (h _ ω).1)
  have e1 : {ω | 1 < rho (env (refl α) ω) ((n : ℤ) + 1)} =
      {ω | rho (env α ω) (-((n : ℤ) + 1)) < 1} := by
    ext ω; simp only [Set.mem_setOf_eq, hpt, ENNReal.one_lt_inv]
  rw [e1]
  have hB : MeasurableSet {v : Fin (n + 1) → ℝ | ∏ j, sfun (v j) < 1} :=
    measurableSet_lt (Finset.measurable_prod _ fun j _ => measurable_sfun.comp
      (measurable_pi_apply j)) measurable_const
  have h := prob_vec_eq hRW (fun j : Fin (n + 1) => bw j) (fun j => fw j)
    (fun a b h => Fin.ext (bw_inj h)) (fun a b h => Fin.ext (fw_inj h)) hB
  simp only [Set.mem_setOf_eq] at h
  have e2 : ∀ ω, rho (env α ω) (-((n : ℤ) + 1)) = ∏ j : Fin (n + 1), sfun (α (bw j) ω) := by
    intro ω; rw [rho_neg, Finset.prod_range]; rfl
  have e3 : ∀ ω, rho (env α ω) ((n : ℤ) + 1) = ∏ j : Fin (n + 1), sfun (α (fw j) ω) := by
    intro ω; rw [rho_pos, Finset.prod_range]; rfl
  simp only [e2, e3]
  exact h

lemma ereal_cmp (p q : ℝ≥0∞) (h : p ≠ ∞ ∨ q ≠ ∞) :
    ((p : EReal) - q < 0 ↔ p < q) ∧ (0 < (p : EReal) - q ↔ q < p) ∧
      ((p : EReal) - q = 0 ↔ p = q) := by
  rcases eq_or_ne p ∞ with rfl | hp
  · have hq : q ≠ ∞ := h.resolve_left (fun h' => h' rfl)
    lift q to NNReal using hq
    simp [EReal.top_sub_coe]
  rcases eq_or_ne q ∞ with rfl | hq
  · lift p to NNReal using hp
    simp
  lift p to NNReal using hp
  lift q to NNReal using hq
  have e : ((p : ℝ≥0∞) : EReal) - ((q : ℝ≥0∞) : EReal) = (((p : ℝ) - (q : ℝ) : ℝ) : EReal) := by
    rw [EReal.coe_sub]; rfl
  rw [e]
  simp only [EReal.coe_lt_coe_iff, EReal.coe_eq_zero, ENNReal.coe_lt_coe, ENNReal.coe_inj]
  refine ⟨?_, ?_, ?_⟩
  · rw [← EReal.coe_zero, EReal.coe_lt_coe_iff, sub_neg]; exact NNReal.coe_lt_coe
  · rw [← EReal.coe_zero, EReal.coe_lt_coe_iff, sub_pos]; exact NNReal.coe_lt_coe
  · rw [sub_eq_zero]; exact NNReal.coe_inj

lemma logpart (hRW : IsRWRE P α X) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1))
    (hdef : LogMomentDefined P α) :
    (seriesGt P α ≠ ∞ ↔ logMoment P α < 0) ∧
      (seriesLt P α ≠ ∞ ↔ 0 < logMoment P α) ∧
      (seriesLt P α = ∞ ∧ seriesGt P α = ∞ ↔ logMoment P α = 0) := by
  have hR := refl_RWRE hRW
  have hnd' : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, refl α 0 ω = c := by
    rintro ⟨c, hc⟩
    apply hnd
    refine ⟨1 - c, ?_⟩
    filter_upwards [hc] with ω h
    unfold refl at h; rw [neg_zero] at h; linarith
  have hrange' : (∀ n ω, 0 ≤ refl α n ω ∧ refl α n ω < 1) ∨
      (∀ n ω, 0 < refl α n ω ∧ refl α n ω ≤ 1) := by
    rcases hrange with h | h
    · right; intro n ω; have := h (-n) ω; unfold refl; constructor <;> linarith
    · left; intro n ω; have := h (-n) ω; unfold refl; constructor <;> linarith
  have hP' := logPos_refl hRW
  have hN' := logNeg_refl hRW
  have hdef' : LogMomentDefined P (refl α) := by
    unfold LogMomentDefined at hdef ⊢; rw [hP', hN']; exact hdef.symm
  have A := proof_1_7_log_moment P α X hRW hnd hrange hdef
  have B := proof_1_7_log_moment P (refl α) (fun n ω => -X n ω) hR hnd' hrange' hdef'
  have hS := seriesGt_refl hRW hrange
  have C := ereal_cmp (logMomentPos P α) (logMomentNeg P α) hdef
  have C' := ereal_cmp (logMomentNeg P α) (logMomentPos P α) hdef.symm
  have i1 : seriesGt P α ≠ ∞ ↔ logMoment P α < 0 := (A.1.trans A.2.1).symm
  have i2 : seriesLt P α ≠ ∞ ↔ 0 < logMoment P α := by
    rw [← hS]
    refine (B.1.trans B.2.1).symm.trans ?_
    unfold logMoment; rw [hP', hN', C'.1, C.2.1]
  refine ⟨i1, i2, ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    have n1 : ¬ logMoment P α < 0 := fun h => (i1.mpr h) h2
    have n2 : ¬ 0 < logMoment P α := fun h => (i2.mpr h) h1
    unfold logMoment at n1 n2 ⊢
    rw [C.1] at n1; rw [C.2.1] at n2; rw [C.2.2]
    exact le_antisymm (not_lt.mp n2) (not_lt.mp n1)
  · intro h0
    constructor
    · by_contra h1; have := i2.mp h1; rw [h0] at this; exact lt_irrefl _ this
    · by_contra h2; have := i1.mp h2; rw [h0] at this; exact lt_irrefl _ this

end Refl

end RWREGlue

open SolomonRWRE.Recurrence in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1)) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) ∧
    (LogMomentDefined P α →
      (seriesGt P α ≠ ∞ ↔ logMoment P α < 0) ∧
      (seriesLt P α ≠ ∞ ↔ 0 < logMoment P α) ∧
      (seriesLt P α = ∞ ∧ seriesGt P α = ∞ ↔ logMoment P α = 0)) := by
  have M := RWREGlue.main3 hRW hnd hrange
  exact ⟨M.1, M.2.1, M.2.2, fun hdef => RWREGlue.logpart hRW hnd hrange hdef⟩
