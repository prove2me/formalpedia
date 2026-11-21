-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.Supplement.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:48:26.625882+00:00
-- url     : https://prove2.me/submissions/d9e83d90-a084-40a2-b8d2-62426d302a23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Efficiency
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula
import Theorems.Thm_ProcurementPoA_DeterministicCap_lemma_5_2

section
/-! Rescaling instances of the procurement auction by `λ > 0`, and capped equilibria
from bid-set equilibria. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement

namespace ProcurementPoA.DeterministicCap.Dev.Scale

variable {n : ℕ}

lemma measurable_div_const (l : ℝ) : Measurable fun c : ℝ => c / l := measurable_id.div_const l

/-- costs multiplied by `l` -/
noncomputable def scaleTypes (l : ℝ) (hl : 0 < l) (D : IndependentTypes n) : IndependentTypes n where
  types i := (fun c => c / l) ⁻¹' D.types i
  measurable_types i := measurable_div_const l (D.measurable_types i)
  law i := (D.law i).map (fun c => l * c)
  probability i := Measure.isProbabilityMeasure_map ((by fun_prop : Measurable fun b : ℝ => l * b)).aemeasurable
  concentrated i := by
    rw [Measure.map_apply ((by fun_prop : Measurable fun b : ℝ => l * b))
      (measurable_div_const l (D.measurable_types i)).compl]
    have e : (fun c => l * c) ⁻¹' ((fun c => c / l) ⁻¹' D.types i)ᶜ = (D.types i)ᶜ := by
      ext c; simp [mul_div_cancel_left₀ _ hl.ne']
    rw [e]; exact D.concentrated i

/-- the tie rule applied to bids divided by `l` -/
noncomputable def scaleTie (l : ℝ) (hl : 0 < l) (τ : TieRule n) : TieRule n where
  select := τ.select.comap (fun b i => b i / l) (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (X := fun _ : Suppliers n => ℝ) i).div_const l)
  markov := by infer_instance
  lowest_only b := by
    rw [Kernel.comap_apply]
    filter_upwards [τ.lowest_only (fun i => b i / l)] with i hi j
    exact (div_le_div_iff_of_pos_right hl).1 (hi j)

/-- a cost-`c` supplier plays like a cost-`c/l` one, with bids multiplied by `l` -/
noncomputable def scaleProfile (l : ℝ) (σ : MixedProfile n) : MixedProfile n where
  bid i := ((σ.bid i).comap (fun c => c / l) (measurable_div_const l)).map (fun b => l * b)
  markov i := Kernel.IsMarkovKernel.map _ ((by fun_prop : Measurable fun b : ℝ => l * b))

section
variable (l : ℝ) (hl : 0 < l) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)

include hl

omit hl in
lemma bid_scale (i : Suppliers n) (c : ℝ) :
    (scaleProfile l σ).bid i c = (σ.bid i (c / l)).map (fun b => l * b) := by
  simp only [scaleProfile]
  rw [Kernel.map_apply _ ((by fun_prop : Measurable fun b : ℝ => l * b)), Kernel.comap_apply]

lemma marg_scale (i : Suppliers n) :
    marginalBidLaw (scaleTypes l hl D) (scaleProfile l σ) i =
      (marginalBidLaw D σ i).map (fun b => l * b) := by
  have hm : Measurable fun b : ℝ => l * b := (by fun_prop : Measurable fun b : ℝ => l * b)
  ext s hs
  rw [Measure.map_apply hm hs]
  unfold marginalBidLaw
  rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    Measure.bind_apply (hm hs) (Kernel.measurable _).aemeasurable]
  show ∫⁻ c, (scaleProfile l σ).bid i c s ∂((D.law i).map (fun c => l * c)) = _
  rw [lintegral_map (Kernel.measurable_coe _ hs) hm]
  congr 1; ext c
  rw [bid_scale l σ, Measure.map_apply hm hs, mul_div_cancel_left₀ _ hl.ne']

/-- coordinatewise multiplication by `l` -/
noncomputable def eL : (Suppliers n → ℝ) ≃ᵐ (Suppliers n → ℝ) :=
  MeasurableEquiv.piCongrRight (fun _ => MeasurableEquiv.mulLeft₀ l hl.ne')

lemma coe_eL : ⇑(eL (n := n) l hl) = fun b i => l * b i := rfl

lemma pi_marg_scale :
    Measure.pi (marginalBidLaw (scaleTypes l hl D) (scaleProfile l σ)) =
      (Measure.pi (marginalBidLaw D σ)).map (eL l hl) := by
  have hm : Measurable fun b : ℝ => l * b := (by fun_prop : Measurable fun b : ℝ => l * b)
  have e : marginalBidLaw (scaleTypes l hl D) (scaleProfile l σ) =
      fun i => (marginalBidLaw D σ i).map (fun b => l * b) := funext (marg_scale l hl D σ)
  have : ∀ i, IsProbabilityMeasure ((marginalBidLaw D σ i).map (fun b => l * b)) :=
    fun i => Measure.isProbabilityMeasure_map hm.aemeasurable
  rw [e, coe_eL, Measure.pi_map_pi (fun i => hm.aemeasurable)]

lemma win_scale (i : Suppliers n) (a : ℝ) :
    interimWin (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) i a =
      interimWin D τ σ i (a / l) := by
  unfold interimWin
  rw [pi_marg_scale, lintegral_map_equiv]
  congr 1; ext bs
  simp only [scaleTie, Kernel.comap_apply]
  congr 2
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h, coe_eL, mul_div_cancel_left₀ _ hl.ne']

lemma std_scale (i : Suppliers n) (c a : ℝ) :
    standardUtility (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) i c a =
      l * standardUtility D τ σ i (c / l) (a / l) := by
  unfold standardUtility
  rw [win_scale]
  have e : l * (a / l - c / l) = a - c := by field_simp
  rw [← mul_assoc, e]

lemma compProd_scale (i : Suppliers n) :
    (scaleTypes l hl D).law i ⊗ₘ (scaleProfile l σ).bid i =
      (D.law i ⊗ₘ σ.bid i).map (Prod.map (fun b => l * b) (fun b => l * b)) := by
  have hm : Measurable fun b : ℝ => l * b := (by fun_prop : Measurable fun b : ℝ => l * b)
  have hp : Measurable (Prod.map (fun b : ℝ => l * b) (fun b : ℝ => l * b)) := hm.prodMap hm
  ext s hs
  rw [Measure.map_apply hp hs, Measure.compProd_apply hs, Measure.compProd_apply (hp hs)]
  show ∫⁻ c, (scaleProfile l σ).bid i c (Prod.mk c ⁻¹' s) ∂((D.law i).map (fun c => l * c)) = _
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hm]
  congr 1; ext c
  rw [bid_scale l σ, Measure.map_apply hm (measurable_prodMk_left hs),
    mul_div_cancel_left₀ _ hl.ne']
  rfl

/-- coordinatewise multiplication of (cost, bid) pairs by `l` -/
noncomputable def eP : (Suppliers n → ℝ × ℝ) ≃ᵐ (Suppliers n → ℝ × ℝ) :=
  MeasurableEquiv.piCongrRight (fun _ =>
    (MeasurableEquiv.mulLeft₀ l hl.ne').prodCongr (MeasurableEquiv.mulLeft₀ l hl.ne'))

lemma coe_eP : ⇑(eP (n := n) l hl) =
    fun x i => Prod.map (fun b => l * b) (fun b => l * b) (x i) := rfl

lemma playLaw_scale :
    playLaw (scaleTypes l hl D) (scaleProfile l σ) = (playLaw D σ).map (eP l hl) := by
  have hm : Measurable fun b : ℝ => l * b := (by fun_prop : Measurable fun b : ℝ => l * b)
  have hp : Measurable (Prod.map (fun b : ℝ => l * b) (fun b : ℝ => l * b)) := hm.prodMap hm
  have e : (fun i => (scaleTypes l hl D).law i ⊗ₘ (scaleProfile l σ).bid i) =
      fun i => (D.law i ⊗ₘ σ.bid i).map (Prod.map (fun b => l * b) (fun b => l * b)) :=
    funext (compProd_scale l hl D σ)
  have : ∀ i, IsProbabilityMeasure
      ((D.law i ⊗ₘ σ.bid i).map (Prod.map (fun b : ℝ => l * b) (fun b : ℝ => l * b))) :=
    fun i => Measure.isProbabilityMeasure_map hp.aemeasurable
  unfold playLaw
  rw [e, coe_eP, Measure.pi_map_pi (fun i => hp.aemeasurable)]

lemma lowest_scale (b : Suppliers n → ℝ) : lowest (fun i => l * b i) = l * lowest b := by
  unfold lowest
  apply le_antisymm
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty b
    rw [hj]; exact Finset.inf'_le _ (Finset.mem_univ j)
  · apply Finset.le_inf'; intro j _
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ j)) hl.le

lemma winner_scale (x : Suppliers n → ℝ × ℝ) :
    winnerCost (scaleTie l hl τ) (eP l hl x) = ENNReal.ofReal l * winnerCost τ x := by
  unfold winnerCost
  rw [Finset.mul_sum]; congr 1; ext i
  simp only [coe_eP, Prod.map_fst, Prod.map_snd, scaleTie, Kernel.comap_apply,
    mul_div_cancel_left₀ _ hl.ne', ENNReal.ofReal_mul hl.le, mul_assoc]

lemma inCost_scale (L U : ℝ) (h : InCostInterval D L U) :
    InCostInterval (scaleTypes l hl D) (l * L) (l * U) := by
  intro i c hc
  obtain ⟨h1, h2⟩ := h i hc
  rw [le_div_iff₀ hl] at h1
  rw [div_le_iff₀ hl] at h2
  constructor <;> linarith

lemma isBidSetBNE_scale (L U : ℝ) (h : IsBidSetBNE D τ σ (Icc L U)) :
    IsBidSetBNE (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) (Icc (l * L) (l * U)) := by
  obtain ⟨hnu, hmem, hbr⟩ := h
  have hemb := measurableEmbedding_mulLeft₀ hl.ne'
  refine ⟨fun i c hc => ?_, fun i c hc => ?_, fun i c hc => ?_⟩
  · rw [bid_scale l σ, hemb.ae_map_iff]
    filter_upwards [hnu i _ hc] with b hb
    have := mul_le_mul_of_nonneg_left hb hl.le
    rwa [mul_div_cancel₀ _ hl.ne'] at this
  · rw [bid_scale l σ, hemb.ae_map_iff]
    filter_upwards [hmem i _ hc] with b hb
    exact ⟨mul_le_mul_of_nonneg_left hb.1 hl.le, mul_le_mul_of_nonneg_left hb.2 hl.le⟩
  · rw [bid_scale l σ, hemb.ae_map_iff]
    filter_upwards [hbr i _ hc] with b hb a ha
    rw [std_scale, std_scale, mul_div_cancel_left₀ _ hl.ne']
    refine mul_le_mul_of_nonneg_left (hb _ ⟨?_, ?_⟩) hl.le
    · rw [le_div_iff₀ hl]; linarith [ha.1]
    · rw [div_le_iff₀ hl]; linarith [ha.2]

lemma standardSocialCost_scale :
    standardSocialCost (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) =
      ENNReal.ofReal l * standardSocialCost D τ σ := by
  unfold standardSocialCost
  rw [playLaw_scale, lintegral_map_equiv]
  simp_rw [winner_scale l hl τ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma optimal_scale : optimalSocialCost (scaleTypes l hl D) = ENNReal.ofReal l * optimalSocialCost D := by
  have hm : Measurable fun b : ℝ => l * b := (by fun_prop : Measurable fun b : ℝ => l * b)
  have e : typeLaw (scaleTypes l hl D) = (typeLaw D).map (eL l hl) := by
    rw [coe_eL]
    unfold typeLaw
    exact (Measure.pi_map_pi (fun i => hm.aemeasurable)).symm
  unfold optimalSocialCost
  rw [e, lintegral_map_equiv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; ext c
  rw [coe_eL, lowest_scale l hl c, ENNReal.ofReal_mul hl.le]

end

/-- an equilibrium with costs in `[1,R]` and bids restricted to `[1,T]` is an equilibrium of the
deterministic cap `T`, with the same social cost (every bid is accepted) -/
lemma isBNE_of_bidSet (R T : ℝ) (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D 1 R) (h : IsBidSetBNE D τ σ (Icc 1 T)) :
    IsBNE D τ σ T ∧ socialCost D τ σ R T = standardSocialCost D τ σ := by
  obtain ⟨hnu, hmem, hbr⟩ := h
  have hTb : ∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c), b ≤ T :=
    fun i c hc => (hmem i c hc).mono fun b hb => hb.2
  refine ⟨⟨hnu, fun i c hc => ?_⟩, ?_⟩
  · filter_upwards [hnu i c hc, hmem i c hc, hbr i c hc] with b hcb hb hbest a
    have hc1 : 1 ≤ c := (hcost i hc).1
    have hub : interimUtility D τ σ T i c b = standardUtility D τ σ i c b := by
      simp only [interimUtility, standardUtility, if_pos hb.2]
    have h0 : 0 ≤ standardUtility D τ σ i c b :=
      mul_nonneg (sub_nonneg.2 hcb) ENNReal.toReal_nonneg
    rw [hub]
    unfold interimUtility
    split_ifs with haT
    · by_cases ha1 : 1 ≤ a
      · exact hbest a ⟨ha1, haT⟩
      · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg) h0
    · exact h0
  · unfold socialCost standardSocialCost
    have hae : ∀ᵐ x ∂(playLaw D σ), ∀ i, (x i).2 ≤ T := by
      rw [ae_all_iff]; intro i
      have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
      apply hq.ae (p := fun y : ℝ × ℝ => y.2 ≤ T)
      rw [Measure.ae_compProd_iff (measurableSet_le measurable_snd measurable_const)]
      filter_upwards [mem_ae_iff.2 (D.concentrated i)] with c hc
      exact hTb i c hc
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    unfold outcomeCost
    have hlow : lowest (fun i => (x i).2) ≤ T :=
      (Finset.inf'_le (fun i => (x i).2) (Finset.mem_univ (0 : Suppliers n))).trans (hx 0)
    rw [if_pos hlow]
    rfl

end ProcurementPoA.DeterministicCap.Dev.Scale
end

section
/-!
# Theorem 4.1 (supplement): the exact `e^{-2}` cost bound

Rescale costs by `1/L` to `[1, U/L]`; the bid-set equilibrium becomes an equilibrium of the
deterministic cap `T = U/L` with the same social cost; Lemma 5.2 bounds it by
`E[gCap T T C*] = (1-ε) E[C*] + ε T`; scale back.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement.Dev.T41

open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Supplement
open ProcurementPoA.DeterministicCap.Dev.Scale

lemma ae_type_mem {n : ℕ} (D : IndependentTypes n) :
    ∀ᵐ c ∂(typeLaw D), ∀ i, c i ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
  exact hq.ae (mem_ae_iff.2 (D.concentrated i))

lemma lowest_mem {n : ℕ} (D : IndependentTypes n) {L U : ℝ} (hcost : InCostInterval D L U)
    (c : Suppliers n → ℝ) (hc : ∀ i, c i ∈ D.types i) : lowest c ∈ Set.Icc L U := by
  refine ⟨Finset.le_inf' _ _ (fun i _ => (hcost i (hc i)).1), ?_⟩
  exact (Finset.inf'_le c (Finset.mem_univ 0)).trans (hcost 0 (hc 0)).2

lemma opt_mem {n : ℕ} (D : IndependentTypes n) {L U : ℝ} (hcost : InCostInterval D L U) :
    ENNReal.ofReal L ≤ optimalSocialCost D ∧ optimalSocialCost D ≤ ENNReal.ofReal U := by
  have : IsProbabilityMeasure (typeLaw D) := by unfold typeLaw; infer_instance
  unfold optimalSocialCost
  constructor
  · calc ENNReal.ofReal L = ∫⁻ _c, ENNReal.ofReal L ∂(typeLaw D) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_type_mem D] with c hc
        exact ENNReal.ofReal_le_ofReal (lowest_mem D hcost c hc).1
  · calc _ ≤ ∫⁻ _c, ENNReal.ofReal U ∂(typeLaw D) := by
          apply lintegral_mono_ae
          filter_upwards [ae_type_mem D] with c hc
          exact ENNReal.ofReal_le_ofReal (lowest_mem D hcost c hc).2
      _ = ENNReal.ofReal U := by simp

lemma eps_pos : 0 < epsilon := Real.exp_pos _

lemma eps_lt_one : epsilon < 1 := Real.exp_lt_one_iff.2 (by norm_num)

/-- `E[gCap T T C*] ≤ (1-ε) E[C*] + ε T` when costs lie in `[1,T]` -/
lemma int_gCap_le {n : ℕ} (D : IndependentTypes n) (T : ℝ) (hT : 1 ≤ T)
    (hcost : InCostInterval D 1 T) :
    ∫⁻ c, ENNReal.ofReal (gCap T T (lowest c)) ∂(typeLaw D) ≤
      ENNReal.ofReal (1 - epsilon) * optimalSocialCost D + ENNReal.ofReal (epsilon * T) := by
  have : IsProbabilityMeasure (typeLaw D) := by unfold typeLaw; infer_instance
  have he := eps_pos
  have he1 := eps_lt_one
  calc ∫⁻ c, ENNReal.ofReal (gCap T T (lowest c)) ∂(typeLaw D)
      ≤ ∫⁻ c, (ENNReal.ofReal (1 - epsilon) * ENNReal.ofReal (lowest c) +
          ENNReal.ofReal (epsilon * T)) ∂(typeLaw D) := by
        apply lintegral_mono_ae
        filter_upwards [ae_type_mem D] with c hc
        obtain ⟨h1, h2⟩ := lowest_mem D hcost c hc
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
          (mul_nonneg (by linarith) (by linarith)) (by nlinarith)]
        apply ENNReal.ofReal_le_ofReal
        unfold gCap
        split_ifs with h
        · nlinarith
        · have : lowest c = T := le_antisymm h2 (not_lt.1 h)
          rw [this]; nlinarith
    _ = ENNReal.ofReal (1 - epsilon) * optimalSocialCost D + ENNReal.ofReal (epsilon * T) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp [optimalSocialCost]

lemma cost_bound (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D L U) (heq : IsBidSetBNE D τ σ (Set.Icc L U)) :
    standardSocialCost D τ σ ≤
      ENNReal.ofReal (1 - epsilon) * optimalSocialCost D + ENNReal.ofReal (epsilon * U) := by
  have hl : 0 < 1 / L := by positivity
  have e1 : 1 / L * L = 1 := by field_simp
  have e2 : 1 / L * U = U / L := by field_simp
  have hT : 1 ≤ U / L := by rw [le_div_iff₀ hL]; linarith
  have hc' := inCost_scale (1 / L) hl D L U hcost
  rw [e1, e2] at hc'
  have hb' := isBidSetBNE_scale (1 / L) hl D τ σ L U heq
  rw [e1, e2] at hb'
  obtain ⟨hB, hS⟩ := isBNE_of_bidSet (U / L) (U / L) _ _ _ hc' hb'
  have h52 := lemma_5_2 (U / L) (U / L) hT hT _ _ _ hc' hB
  rw [hS, standardSocialCost_scale] at h52
  have h := h52.trans (int_gCap_le _ (U / L) hT hc')
  rw [optimal_scale] at h
  have hLl : ENNReal.ofReal L * ENNReal.ofReal (1 / L) = 1 := by
    rw [← ENNReal.ofReal_mul hL.le, mul_comm, e1, ENNReal.ofReal_one]
  have hm := mul_le_mul_right h (ENNReal.ofReal L)
  have hA : ENNReal.ofReal L * (ENNReal.ofReal (1 - epsilon) *
      (ENNReal.ofReal (1 / L) * optimalSocialCost D)) =
      ENNReal.ofReal (1 - epsilon) * optimalSocialCost D := by
    rw [mul_left_comm, ← mul_assoc (ENNReal.ofReal L), hLl, one_mul]
  rw [← mul_assoc, hLl, one_mul, mul_add, hA, ← ENNReal.ofReal_mul hL.le] at hm
  have e3 : L * (epsilon * (U / L)) = epsilon * U := by field_simp
  rwa [e3] at hm

end ProcurementPoA.DeterministicCap.Supplement.Dev.T41

namespace ProcurementPoA.DeterministicCap.Supplement

open ProcurementPoA.DeterministicCap.Supplement.Dev.T41

/-- The exact e^(-2) cost bound and both ratio inequalities. -/
theorem chk_theorem_4_1 (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D L U) (heq : IsBidSetBNE D τ σ (Set.Icc L U)) :
    standardSocialCost D τ σ ≤
      ENNReal.ofReal (1 - epsilon) * optimalSocialCost D + ENNReal.ofReal (epsilon * U) ∧
    standardSocialCost D τ σ / optimalSocialCost D ≤
      ENNReal.ofReal (1 + epsilon * (U / (optimalSocialCost D).toReal - 1)) ∧
    1 + epsilon * (U / (optimalSocialCost D).toReal - 1) ≤
      1 + epsilon * (U / L - 1) := by
  have h1 := cost_bound L U hL hLU D τ σ hcost heq
  obtain ⟨hlo, hhi⟩ := opt_mem D hcost
  have hne : optimalSocialCost D ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  set o := (optimalSocialCost D).toReal with ho
  have hoL : L ≤ o := by
    have := ENNReal.toReal_mono hne hlo
    rwa [ENNReal.toReal_ofReal hL.le] at this
  have ho0 : 0 < o := lt_of_lt_of_le hL hoL
  have he := eps_pos
  have he1 := eps_lt_one
  have hU0 : 0 ≤ U := by linarith
  refine ⟨h1, ?_, ?_⟩
  · apply ENNReal.div_le_of_le_mul
    have hopt : optimalSocialCost D = ENNReal.ofReal o := (ENNReal.ofReal_toReal hne).symm
    have hpos : 0 ≤ 1 + epsilon * (U / o - 1) := by
      have : 0 ≤ U / o := by positivity
      nlinarith
    rw [hopt, ← ENNReal.ofReal_mul hpos]
    rw [hopt, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add
      (mul_nonneg (by linarith) ho0.le) (by positivity)] at h1
    refine h1.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    field_simp
    ring
  · have : U / o ≤ U / L := div_le_div_of_nonneg_left hU0 hL hoL
    nlinarith

end ProcurementPoA.DeterministicCap.Supplement
end

open ProcurementPoA.DeterministicCap.Supplement in
theorem solution : type_of% @ProcurementPoA.DeterministicCap.Supplement.chk_theorem_4_1 := @ProcurementPoA.DeterministicCap.Supplement.chk_theorem_4_1
