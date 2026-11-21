-- Prove2me | solution 1 for ProcurementPoA.DeterministicCap.theorem_5_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:48:27.120421+00:00
-- url     : https://prove2.me/submissions/3d0fe2f5-b34f-4c38-bb16-1bc7df04b0e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Efficiency
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula
import Theorems.Thm_ProcurementPoA_DeterministicCap_lemma_5_2
import Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_remark_4_2
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

lemma util_scale (T : ℝ) (i : Suppliers n) (c a : ℝ) :
    interimUtility (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) (l * T) i c a =
      l * interimUtility D τ σ T i (c / l) (a / l) := by
  unfold interimUtility
  rw [win_scale]
  have hiff : a ≤ l * T ↔ a / l ≤ T := by rw [div_le_iff₀ hl, mul_comm]
  have e : l * (a / l - c / l) = a - c := by field_simp
  by_cases h : a / l ≤ T
  · rw [if_pos (hiff.2 h), if_pos h, ← mul_assoc, e]
  · rw [if_neg (mt hiff.1 h), if_neg h, mul_zero]

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

lemma outcome_scale (U T : ℝ) (x : Suppliers n → ℝ × ℝ) :
    outcomeCost (scaleTie l hl τ) (l * U) (l * T) (eP l hl x) =
      ENNReal.ofReal l * outcomeCost τ U T x := by
  have hlow : lowest (fun i => (eP l hl x i).2) = l * lowest (fun i => (x i).2) :=
    lowest_scale l hl (fun i => (x i).2)
  unfold outcomeCost
  rw [hlow]
  by_cases h : lowest (fun i => (x i).2) ≤ T
  · rw [if_pos (mul_le_mul_of_nonneg_left h hl.le), if_pos h]
    exact winner_scale l hl τ x
  · rw [if_neg (fun h' => h (le_of_mul_le_mul_left h' hl)), if_neg h, ENNReal.ofReal_mul hl.le]

lemma inCost_scale (L U : ℝ) (h : InCostInterval D L U) :
    InCostInterval (scaleTypes l hl D) (l * L) (l * U) := by
  intro i c hc
  obtain ⟨h1, h2⟩ := h i hc
  rw [le_div_iff₀ hl] at h1
  rw [div_le_iff₀ hl] at h2
  constructor <;> linarith

lemma isBNE_scale (T : ℝ) (h : IsBNE D τ σ T) :
    IsBNE (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) (l * T) := by
  obtain ⟨hnu, hbr⟩ := h
  have hemb := measurableEmbedding_mulLeft₀ hl.ne'
  refine ⟨fun i c hc => ?_, fun i c hc => ?_⟩
  · rw [bid_scale l σ, hemb.ae_map_iff]
    filter_upwards [hnu i _ hc] with b hb
    have := mul_le_mul_of_nonneg_left hb hl.le
    rwa [mul_div_cancel₀ _ hl.ne'] at this
  · rw [bid_scale l σ, hemb.ae_map_iff]
    filter_upwards [hbr i _ hc] with b hb a
    rw [util_scale, util_scale, mul_div_cancel_left₀ _ hl.ne']
    exact mul_le_mul_of_nonneg_left (hb _) hl.le

lemma socialCost_scale (U T : ℝ) :
    socialCost (scaleTypes l hl D) (scaleTie l hl τ) (scaleProfile l σ) (l * U) (l * T) =
      ENNReal.ofReal l * socialCost D τ σ U T := by
  unfold socialCost
  rw [playLaw_scale, lintegral_map_equiv]
  simp_rw [outcome_scale l hl τ U T]
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

/-- the scaling identity of Theorem 5.3 -/
lemma poaOn_scale (L U : ℝ) (hL : 0 < L) (T : ℝ) : poaOn L U (L * T) = poa (U / L) T := by
  unfold poa poaOn
  congr 1
  ext q
  simp only [equilibriumRatios, Set.mem_ofPred_eq]
  have e1 : 1 / L * L = 1 := by field_simp
  have e2 : 1 / L * U = U / L := by field_simp
  have e3 : 1 / L * (L * T) = T := by field_simp
  have e4 : L * (U / L) = U := by field_simp
  constructor
  · rintro ⟨n, D, τ, σ, hc, hb, rfl⟩
    have hl : 0 < 1 / L := by positivity
    refine ⟨n, scaleTypes (1 / L) hl D, scaleTie (1 / L) hl τ, scaleProfile (1 / L) σ, ?_, ?_, ?_⟩
    · have := inCost_scale (1 / L) hl D L U hc
      rwa [e1, e2] at this
    · have := isBNE_scale (1 / L) hl D τ σ (L * T) hb
      rwa [e3] at this
    · have h1 := socialCost_scale (1 / L) hl D τ σ U (L * T)
      rw [e2, e3] at h1
      rw [h1, optimal_scale, ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hl).ne'
        ENNReal.ofReal_ne_top]
  · rintro ⟨n, D, τ, σ, hc, hb, rfl⟩
    refine ⟨n, scaleTypes L hL D, scaleTie L hL τ, scaleProfile L σ, ?_, ?_, ?_⟩
    · have := inCost_scale L hL D 1 (U / L) hc
      rwa [mul_one, e4] at this
    · exact isBNE_scale L hL D τ σ T hb
    · have h1 := socialCost_scale L hL D τ σ (U / L) T
      rw [e4] at h1
      rw [h1, optimal_scale, ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hL).ne'
        ENNReal.ofReal_ne_top]

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
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
lemma epsilon_pos : 0 < epsilon := Real.exp_pos _

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
/-! Blueprint for Theorem 5.3. Every `sorry` is a stub proved in a Part. -/
/-! ## Part Q: the formulas (pure real analysis) -/
alias epsilon_pos := ProcurementPoA.DeterministicCap.Dev.T53.PartQ.epsilon_pos

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma eps_mul_E : epsilon * Real.exp 2 = 1 := by
  unfold epsilon; rw [← Real.exp_add]; simp

lemma E_gt_one : 1 < Real.exp 2 := by
  have := Real.add_one_lt_exp (x := (2:ℝ)) (by norm_num); linarith

lemma epsilon_lt_one : epsilon < 1 := by
  unfold epsilon; rw [show (1:ℝ) = Real.exp 0 by simp]; exact Real.exp_lt_exp.mpr (by norm_num)

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
/-- the square root inside `capStar` -/
lemma sq_s (R : ℝ) (hR : 0 ≤ R) :
    Real.sqrt ((Real.exp 2 - 1) ^ 2 + 4 * Real.exp 2 * R) ^ 2
      = (Real.exp 2 - 1) ^ 2 + 4 * Real.exp 2 * R := by
  rw [Real.sq_sqrt]; have := E_gt_one; positivity

lemma capStar_eqn (R : ℝ) (hR : 0 ≤ R) :
    capStar R ^ 2 + (Real.exp 2 - 1) * capStar R = Real.exp 2 * R := by
  have h := sq_s R hR
  unfold capStar
  linear_combination h / 4

lemma capBound_formula (R : ℝ) (hR : 0 ≤ R) :
    capBound R = 1 + epsilon * (capStar R - 1) := by
  set s := Real.sqrt ((Real.exp 2 - 1) ^ 2 + 4 * Real.exp 2 * R) with hs
  have h := sq_s R hR
  rw [← hs] at h
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have e1 := eps_mul_E
  have ep := epsilon_pos
  have key : Real.sqrt ((1 - epsilon) ^ 2 + 4 * epsilon * R) = epsilon * s := by
    rw [show (1 - epsilon) ^ 2 + 4 * epsilon * R = (epsilon * s) ^ 2 by
      linear_combination (-epsilon ^ 2) * h
        + (-1 + 2 * epsilon - epsilon * Real.exp 2 - 4 * epsilon * R) * e1]
    exact Real.sqrt_sq (by positivity)
  unfold capBound capStar
  rw [key, ← hs]
  linear_combination (1/2 : ℝ) * e1

lemma capStar_facts (R : ℝ) (hR : 1 ≤ R) :
    1 ≤ capStar R ∧ capStar R ≤ R ∧ (1 < R → 1 < capStar R ∧ capStar R < R) := by
  have h := sq_s R (by linarith)
  have hE := E_gt_one
  set s := Real.sqrt ((Real.exp 2 - 1) ^ 2 + 4 * Real.exp 2 * R) with hs
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc : capStar R = (s - (Real.exp 2 - 1)) / 2 := rfl
  rw [hc]
  refine ⟨?_, ?_, fun h1 => ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma capBound_eq_left (R : ℝ) (hR : 1 ≤ R) : capBound R = 1 + epsilon * (capStar R - 1) :=
  capBound_formula R (by linarith)

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma capBound_eq_right (R : ℝ) (hR : 1 ≤ R) : capBound R = R / capStar R := by
  have hT := (capStar_facts R hR).1
  have h := capStar_eqn R (by linarith)
  have e1 := eps_mul_E
  rw [capBound_formula R (by linarith), eq_div_iff (by linarith)]
  linear_combination epsilon * h + (R - capStar R) * e1

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
/-- the minimax property of `capStar` -/
lemma capBound_le_max (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T) :
    capBound R ≤ max (1 + epsilon * (T - 1)) (R / T) := by
  have hT1 := (capStar_facts R hR).1
  rcases le_total T (capStar R) with h | h
  · apply le_max_of_le_right
    rw [capBound_eq_right R hR]
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) h
  · apply le_max_of_le_left
    rw [capBound_eq_left R hR]
    have := epsilon_pos
    nlinarith

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma capBound_le_R (R : ℝ) (hR : 1 ≤ R) : capBound R ≤ R := by
  rw [capBound_eq_right R hR]
  exact div_le_self (by linarith) (capStar_facts R hR).1

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma capBound_asymp :
    ∃ K : ℝ, 0 < K ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      |capBound R - Real.sqrt R / Real.exp 1 - (1 - epsilon) / 2| ≤ K / Real.sqrt R := by
  refine ⟨1, one_pos, 1, le_rfl, fun R hR => ?_⟩
  have ep := epsilon_pos
  have el := epsilon_lt_one
  set u := Real.sqrt R with hu
  have u1 : 1 ≤ u := by rw [hu]; exact Real.one_le_sqrt.mpr hR
  have uu : u ^ 2 = R := Real.sq_sqrt (by linarith)
  have epe : epsilon = (Real.exp 1)⁻¹ ^ 2 := by
    unfold epsilon; rw [← Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have e0 : 0 < Real.exp 1 := Real.exp_pos 1
  have e4 : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9; linarith
  set w := 2 * u / Real.exp 1 with hw
  have w0 : 0 < w := by positivity
  have wsq : w ^ 2 = 4 * epsilon * R := by
    rw [hw, epe, ← uu]; field_simp; norm_num
  set v := Real.sqrt ((1 - epsilon) ^ 2 + 4 * epsilon * R) with hv
  have v0 : 0 ≤ v := Real.sqrt_nonneg _
  have vsq : v ^ 2 = (1 - epsilon) ^ 2 + w ^ 2 := by
    rw [hv, Real.sq_sqrt (by positivity), wsq]
  have hvw : w ≤ v := by nlinarith
  have hb : (v - w) * w ≤ 1 := by nlinarith
  have hcb : capBound R - u / Real.exp 1 - (1 - epsilon) / 2 = (v - w) / 2 := by
    unfold capBound; rw [← hv, hw]; ring
  rw [hcb, abs_of_nonneg (by linarith), div_le_div_iff₀ (by norm_num) (by linarith)]
  -- (v - w) * u ≤ 2 since (v-w) * w ≤ 1 and w = 2u/e ≥ u/2
  have hwu : u ≤ 2 * w := by
    rw [hw, mul_div_assoc', le_div_iff₀ e0]; nlinarith
  nlinarith

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
lemma capStar_tendsto :
    Tendsto (fun R : ℝ => capStar R / (Real.exp 1 * Real.sqrt R)) atTop (𝓝 1) := by
  have e0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hE : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  set a := Real.exp 2 - 1
  have hlow : Tendsto (fun R : ℝ => 1 - a / Real.exp 1 * (Real.sqrt R)⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun R : ℝ => (Real.sqrt R)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    simpa using (h1.const_mul (a / Real.exp 1)).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hT := (capStar_facts R hR).1
    have h := capStar_eqn R (by linarith)
    have u1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
    have uu : Real.sqrt R ^ 2 = R := Real.sq_sqrt (by linarith)
    have ha : 0 < a := by have := E_gt_one; simp only [a]; linarith
    have key : Real.exp 1 * Real.sqrt R - a ≤ capStar R := by
      have h2 : capStar R ^ 2 + a * capStar R = (Real.exp 1 * Real.sqrt R) ^ 2 := by
        rw [mul_pow, uu, ← hE]; exact h
      by_contra hc
      replace hc := not_le.mp hc
      have eu := mul_pos e0 (show (0:ℝ) < Real.sqrt R by linarith)
      nlinarith [mul_pos (show (0:ℝ) < Real.exp 1 * Real.sqrt R - (capStar R + a) by linarith)
        (show (0:ℝ) < capStar R by linarith),
        mul_pos (show (0:ℝ) < Real.exp 1 * Real.sqrt R - capStar R by linarith) eu]
    rw [le_div_iff₀ (by positivity)]
    have : a / Real.exp 1 * (Real.sqrt R)⁻¹ * (Real.exp 1 * Real.sqrt R) = a := by
      field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    have hT := (capStar_facts R hR).1
    have h := capStar_eqn R (by linarith)
    have u1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
    have uu : Real.sqrt R ^ 2 = R := Real.sq_sqrt (by linarith)
    have ha : 0 < a := by have := E_gt_one; simp only [a]; linarith
    rw [div_le_one (by positivity)]
    have h2 : capStar R ^ 2 + a * capStar R = (Real.exp 1 * Real.sqrt R) ^ 2 := by
      rw [mul_pow, uu, ← hE]; exact h
    by_contra hc
    replace hc := not_le.mp hc
    have eu := mul_pos e0 (show (0:ℝ) < Real.sqrt R by linarith)
    nlinarith [mul_pos (show (0:ℝ) < capStar R - Real.exp 1 * Real.sqrt R by linarith)
      (show (0:ℝ) < capStar R + Real.exp 1 * Real.sqrt R by linarith)]

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartP
open ProcurementPoA.DeterministicCap.Dev.T53
open ProbabilityTheory
/-! ### generic a.e. facts -/
lemma ae_type_mem {n : ℕ} (D : IndependentTypes n) :
    ∀ᵐ c ∂(typeLaw D), ∀ i, c i ∈ D.types i := by
  rw [ae_all_iff]
  intro i
  have hq := (measurePreserving_eval D.law i).quasiMeasurePreserving
  exact hq.ae (mem_ae_iff.2 (D.concentrated i))

lemma lowest_mem {n : ℕ} (D : IndependentTypes n) {L U : ℝ} (hcost : InCostInterval D L U)
    (c : Suppliers n → ℝ) (hc : ∀ i, c i ∈ D.types i) : lowest c ∈ Icc L U := by
  refine ⟨Finset.le_inf' _ _ (fun i _ => (hcost i (hc i)).1), ?_⟩
  exact (Finset.inf'_le c (Finset.mem_univ 0)).trans (hcost 0 (hc 0)).2

lemma one_le_opt {n : ℕ} (D : IndependentTypes n) {R : ℝ} (hcost : InCostInterval D 1 R) :
    1 ≤ optimalSocialCost D := by
  have : IsProbabilityMeasure (typeLaw D) := by unfold typeLaw; infer_instance
  unfold optimalSocialCost
  calc (1 : ℝ≥0∞) = ∫⁻ _c, ENNReal.ofReal 1 ∂(typeLaw D) := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_type_mem D] with c hc
      exact ENNReal.ofReal_le_ofReal (lowest_mem D hcost c hc).1

/-! ### Dirac helpers -/
lemma ae_pi_dirac {n : ℕ} {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Fin (n + 1) → Measure α) (p : Fin (n + 1) → α) (h : ∀ j, μ j = Measure.dirac (p j))
    [∀ j, IsProbabilityMeasure (μ j)] : ∀ᵐ x ∂(Measure.pi μ), x = p := by
  have : ∀ j, ∀ᵐ x ∂(Measure.pi μ), x j = p j := by
    intro j
    have hq := (measurePreserving_eval μ j).quasiMeasurePreserving
    exact hq.ae (p := fun y : α => y = p j) (by rw [h j, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl)
  filter_upwards [ae_all_iff.2 this] with x hx
  exact funext hx

lemma dirac_compProd_dirac (a b : ℝ) (κ : ProbabilityTheory.Kernel ℝ ℝ)
    [ProbabilityTheory.IsMarkovKernel κ] (h : κ a = Measure.dirac b) :
    Measure.dirac a ⊗ₘ κ = Measure.dirac (a, b) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_dirac' _
    (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hs), h,
    Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
  rfl

/-! ### the one-supplier instance: cost `c`, bid `R + 1` -/
/-- the trivial tie rule for one supplier -/
noncomputable def tie1 : TieRule 0 where
  select := ProbabilityTheory.Kernel.const _ (Measure.dirac 0)
  markov := inferInstance
  lowest_only b := by
    refine Filter.Eventually.of_forall (fun i j => ?_)
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]

noncomputable def D1 (c : ℝ) : IndependentTypes 0 := Supplement.deterministicTypes (fun _ => c)

noncomputable def prof1 (B : ℝ) : MixedProfile 0 where
  bid _ := ProbabilityTheory.Kernel.const ℝ (Measure.dirac B)
  markov _ := inferInstance

lemma lowest_const {n : ℕ} (a : ℝ) : lowest (fun _ : Suppliers n => a) = a := by
  unfold lowest
  exact Finset.inf'_const _ _

lemma ratio_mem (R T c : ℝ) (hc : c ∈ Icc 1 R) (hTc : T ≤ c) :
    ENNReal.ofReal (R / c) ∈ equilibriumRatios 1 R T := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hTB : T < R + 1 := by linarith [hc.2]
  refine ⟨0, D1 c, tie1, prof1 (R + 1), ?_, ⟨?_, ?_⟩, ?_⟩
  · intro i x hx
    have : x = c := hx
    rw [this]; exact hc
  · intro i x hx
    have : x = c := hx
    simp only [prof1, ProbabilityTheory.Kernel.const_apply, ae_dirac_eq]
    exact Filter.eventually_pure.2 (by rw [this]; linarith [hc.2])
  · intro i x hx
    have : x = c := hx
    simp only [prof1, ProbabilityTheory.Kernel.const_apply, ae_dirac_eq]
    refine Filter.eventually_pure.2 (fun a => ?_)
    unfold interimUtility
    rw [if_neg (not_le.2 hTB)]
    split_ifs with ha
    · exact mul_nonpos_of_nonpos_of_nonneg (by rw [this]; linarith) ENNReal.toReal_nonneg
    · exact le_rfl
  · have hplay : ∀ᵐ x ∂(playLaw (D1 c) (prof1 (R + 1))), x = fun _ => (c, R + 1) :=
      ae_pi_dirac _ _ (fun j => dirac_compProd_dirac c (R + 1) _
        (ProbabilityTheory.Kernel.const_apply _ _))
    have htype : ∀ᵐ x ∂(typeLaw (D1 c)), x = fun _ => c := ae_pi_dirac _ _ (fun j => rfl)
    have : IsProbabilityMeasure (playLaw (D1 c) (prof1 (R + 1))) := by
      unfold playLaw; infer_instance
    have : IsProbabilityMeasure (typeLaw (D1 c)) := by unfold typeLaw; infer_instance
    have hSC : socialCost (D1 c) tie1 (prof1 (R + 1)) R T = ENNReal.ofReal R := by
      unfold socialCost
      rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal R)]
      · simp
      · filter_upwards [hplay] with x hx
        subst hx
        unfold outcomeCost
        rw [if_neg (by rw [lowest_const]; exact not_le.2 hTB)]
    have hOPT : optimalSocialCost (D1 c) = ENNReal.ofReal c := by
      unfold optimalSocialCost
      rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal c)]
      · simp
      · filter_upwards [htype] with x hx
        subst hx
        rw [lowest_const]
    rw [hSC, hOPT, ENNReal.ofReal_div_of_pos hc0]

/-! ## Part P targets -/
/-- upper bound, from Lemma 5.2 -/
lemma poa_le (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    poa R T ≤ ENNReal.ofReal (max (1 + epsilon * (T - 1)) (R / T)) := by
  unfold poa poaOn
  apply sSup_le
  rintro q ⟨n, D, τ, σ, hc, hb, rfl⟩
  have h1 := lemma_5_2 R T hR hT D τ σ hc hb
  set K := max (1 + epsilon * (T - 1)) (R / T) with hK
  have he := epsilon_pos
  have hT0 : 0 < T := by linarith
  have hK0 : 0 ≤ K := le_trans (by nlinarith) (le_max_left _ _)
  have h2 : ∫⁻ c, ENNReal.ofReal (gCap R T (lowest c)) ∂(typeLaw D) ≤
      optimalSocialCost D * ENNReal.ofReal K := by
    unfold optimalSocialCost
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_type_mem D] with c hc'
    obtain ⟨hl1, hlR⟩ := lowest_mem D hc c hc'
    rw [← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    set x := lowest c
    unfold gCap
    split_ifs with hxT
    · calc x + epsilon * (T - x) ≤ (1 + epsilon * (T - 1)) * x := by
              nlinarith [mul_nonneg (mul_nonneg he.le hT0.le) (sub_nonneg.2 hl1)]
        _ ≤ x * K := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    · rw [not_lt] at hxT
      calc R = R / T * T := by field_simp
        _ ≤ R / T * x := mul_le_mul_of_nonneg_left hxT (by positivity)
        _ ≤ x * K := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  exact ENNReal.div_le_of_le_mul' (h1.trans h2)

end ProcurementPoA.DeterministicCap.Dev.T53.PartP
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
/-! ## Part P: the price of anarchy of the deterministic cap -/
alias poa_le := ProcurementPoA.DeterministicCap.Dev.T53.PartP.poa_le

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartP
open ProcurementPoA.DeterministicCap.Dev.T53
open ProbabilityTheory
/-- one supplier of cost `T` bidding above `R`: never accepted -/
lemma poa_ge_div (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ENNReal.ofReal (R / T) ≤ poa R T :=
  le_sSup (ratio_mem R T T ⟨hT, hTR⟩ le_rfl)

end ProcurementPoA.DeterministicCap.Dev.T53.PartP
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
alias poa_ge_div := ProcurementPoA.DeterministicCap.Dev.T53.PartP.poa_ge_div

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartP
open ProcurementPoA.DeterministicCap.Dev.T53
open ProbabilityTheory
/-- the instances of Remark 4.2 with `[L,U] = [1,T]` -/
lemma poa_ge_eps (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    ENNReal.ofReal (1 + epsilon * (T - 1)) ≤ poa R T := by
  have key : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (1 + epsilon * (T - 1) - δ) ≤ poa R T := by
    intro δ hδ
    obtain ⟨n, D, τ, σ, hc, hb, hq⟩ := Supplement.remark_4_2 1 T one_pos hT δ hδ
    have hcR : InCostInterval D 1 R := fun i x hx => ⟨(hc i hx).1, (hc i hx).2.trans hTR⟩
    obtain ⟨hB, hS⟩ := Dev.Scale.isBNE_of_bidSet R T D τ σ hcR hb
    rw [div_one] at hq
    refine hq.trans (le_sSup ⟨n, D, τ, σ, hcR, hB, ?_⟩)
    rw [hS]
  refine le_of_forall_lt_imp_le_of_dense fun q hq => ?_
  have hqt : q ≠ ⊤ := ne_top_of_lt hq
  have hlt : q.toReal < 1 + epsilon * (T - 1) := by
    have := (ENNReal.toReal_lt_toReal hqt ENNReal.ofReal_ne_top).2 hq
    rwa [ENNReal.toReal_ofReal (by nlinarith [epsilon_pos])] at this
  have := key (1 + epsilon * (T - 1) - q.toReal) (by linarith)
  rwa [sub_sub_cancel, ENNReal.ofReal_toReal hqt] at this

end ProcurementPoA.DeterministicCap.Dev.T53.PartP
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
alias poa_ge_eps := ProcurementPoA.DeterministicCap.Dev.T53.PartP.poa_ge_eps

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartP
open ProcurementPoA.DeterministicCap.Dev.T53
open ProbabilityTheory
/-- below the lowest cost nothing is ever accepted -/
lemma poa_lt_one (R T : ℝ) (hR : 1 ≤ R) (hT : T < 1) : poa R T = ENNReal.ofReal R := by
  apply le_antisymm
  · unfold poa poaOn
    apply sSup_le
    rintro q ⟨n, D, τ, σ, hc, ⟨hnu, -⟩, rfl⟩
    have : IsProbabilityMeasure (playLaw D σ) := by unfold playLaw; infer_instance
    have hae : ∀ᵐ x ∂(playLaw D σ), ∀ i, T < (x i).2 := by
      rw [ae_all_iff]; intro i
      have hq := (measurePreserving_eval (fun i => D.law i ⊗ₘ σ.bid i) i).quasiMeasurePreserving
      apply hq.ae (p := fun y : ℝ × ℝ => T < y.2)
      rw [Measure.ae_compProd_iff (measurableSet_lt measurable_const measurable_snd)]
      filter_upwards [mem_ae_iff.2 (D.concentrated i)] with c hc'
      filter_upwards [hnu i c hc'] with b hb
      linarith [(hc i hc').1]
    have hSC : socialCost D τ σ R T = ENNReal.ofReal R := by
      unfold socialCost
      rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal R)]
      · simp
      · filter_upwards [hae] with x hx
        unfold outcomeCost
        rw [if_neg (show ¬ lowest (fun i => (x i).2) ≤ T from
          not_le.2 ((Finset.lt_inf'_iff _).2 fun i _ => hx i))]
    rw [hSC]
    calc ENNReal.ofReal R / optimalSocialCost D ≤ ENNReal.ofReal R / 1 :=
          ENNReal.div_le_div_left (one_le_opt D hc) _
      _ = ENNReal.ofReal R := div_one _
  · have := le_sSup (ratio_mem R T 1 ⟨le_rfl, hR⟩ hT.le)
    rwa [div_one] at this

end ProcurementPoA.DeterministicCap.Dev.T53.PartP
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
alias poa_lt_one := ProcurementPoA.DeterministicCap.Dev.T53.PartP.poa_lt_one

lemma poa_eq (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ≤ R) :
    poa R T = ENNReal.ofReal (max (1 + epsilon * (T - 1)) (R / T)) :=
  le_antisymm (poa_le R T hR hT hTR)
    (by
      rcases le_total (1 + epsilon * (T - 1)) (R / T) with h | h
      · rw [max_eq_right h]; exact poa_ge_div R T hR hT hTR
      · rw [max_eq_left h]; exact poa_ge_eps R T hR hT hTR)

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53.PartQ
open ProcurementPoA.DeterministicCap.Dev.T53
theorem theorem_5_3_dev :
    (∀ R : ℝ, 1 ≤ R →
      1 ≤ capStar R ∧ capStar R ≤ R ∧
      (1 < R → 1 < capStar R ∧ capStar R < R) ∧
      poa R (capStar R) = ENNReal.ofReal (capBound R) ∧
      capBound R = 1 + epsilon * (capStar R - 1) ∧
      capBound R = R / capStar R ∧
      (∀ T : ℝ, 1 ≤ T → T ≤ R →
        poa R T = ENNReal.ofReal (max (1 + epsilon * (T - 1)) (R / T))) ∧
      (∀ T : ℝ, T < 1 → poa R T = ENNReal.ofReal R) ∧
      (∀ T : ℝ, T ≤ R → poa R (capStar R) ≤ poa R T)) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      |(poa R (capStar R)).toReal - Real.sqrt R / Real.exp 1 - (1 - epsilon) / 2|
        ≤ K / Real.sqrt R) ∧
    Tendsto (fun R : ℝ => capStar R / (Real.exp 1 * Real.sqrt R)) atTop (𝓝 1) ∧
    (∀ L U : ℝ, 0 < L → L ≤ U → ∀ T : ℝ,
      poaOn L U (L * T) = poa (U / L) T) := by
  have hstar : ∀ R : ℝ, 1 ≤ R → poa R (capStar R) = ENNReal.ofReal (capBound R) := by
    intro R hR
    obtain ⟨h1, h2, -⟩ := capStar_facts R hR
    rw [poa_eq R (capStar R) hR h1 h2, ← capBound_eq_left R hR, ← capBound_eq_right R hR,
      max_self]
  refine ⟨fun R hR => ?_, ?_, capStar_tendsto, fun L U hL _ T => Dev.Scale.poaOn_scale L U hL T⟩
  · obtain ⟨h1, h2, h3⟩ := capStar_facts R hR
    refine ⟨h1, h2, h3, hstar R hR, capBound_eq_left R hR, capBound_eq_right R hR,
      fun T hT hTR => poa_eq R T hR hT hTR, fun T hT => poa_lt_one R T hR hT, fun T hTR => ?_⟩
    rw [hstar R hR]
    rcases lt_or_ge T 1 with hT | hT
    · rw [poa_lt_one R T hR hT]
      exact ENNReal.ofReal_le_ofReal (capBound_le_R R hR)
    · rw [poa_eq R T hR hT hTR]
      exact ENNReal.ofReal_le_ofReal (capBound_le_max R T hR hT)
  · obtain ⟨K, hK, R₀, hR₀, hb⟩ := capBound_asymp
    refine ⟨K, hK, R₀, hR₀, fun R hR => ?_⟩
    have hR1 : 1 ≤ R := le_trans hR₀ hR
    have hc0 : 0 ≤ capBound R := by
      rw [capBound_eq_left R hR1]
      have := epsilon_pos
      nlinarith [(capStar_facts R hR1).1]
    rw [hstar R hR1, ENNReal.toReal_ofReal hc0]
    exact hb R hR

end ProcurementPoA.DeterministicCap.Dev.T53.PartQ
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
namespace ProcurementPoA.DeterministicCap.Dev.T53
/-! ## Assembly -/
alias theorem_5_3_dev := ProcurementPoA.DeterministicCap.Dev.T53.PartQ.theorem_5_3_dev

end ProcurementPoA.DeterministicCap.Dev.T53
end

section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ProcurementPoA.DeterministicCap
open ProcurementPoA
open ProcurementPoA.DeterministicCap
open ProcurementPoA.DeterministicCap.Dev
open ProcurementPoA.DeterministicCap.Dev.T53
theorem solution :
    (∀ R : ℝ, 1 ≤ R →
      1 ≤ capStar R ∧ capStar R ≤ R ∧
      (1 < R → 1 < capStar R ∧ capStar R < R) ∧
      poa R (capStar R) = ENNReal.ofReal (capBound R) ∧
      capBound R = 1 + epsilon * (capStar R - 1) ∧
      capBound R = R / capStar R ∧
      (∀ T : ℝ, 1 ≤ T → T ≤ R →
        poa R T = ENNReal.ofReal (max (1 + epsilon * (T - 1)) (R / T))) ∧
      (∀ T : ℝ, T < 1 → poa R T = ENNReal.ofReal R) ∧
      (∀ T : ℝ, T ≤ R → poa R (capStar R) ≤ poa R T)) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      |(poa R (capStar R)).toReal - Real.sqrt R / Real.exp 1 - (1 - epsilon) / 2|
        ≤ K / Real.sqrt R) ∧
    Tendsto (fun R : ℝ => capStar R / (Real.exp 1 * Real.sqrt R)) atTop (𝓝 1) ∧
    (∀ L U : ℝ, 0 < L → L ≤ U → ∀ T : ℝ,
      poaOn L U (L * T) = poa (U / L) T) := by
  exact ProcurementPoA.DeterministicCap.Dev.T53.theorem_5_3_dev
end
