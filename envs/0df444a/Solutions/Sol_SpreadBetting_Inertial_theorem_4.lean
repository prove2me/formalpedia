-- Prove2me | solution 1 for SpreadBetting.Inertial.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:46:34.504996+00:00
-- url     : https://prove2.me/submissions/b7fd0ed8-10c3-4251-a2d2-2f875567b44c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain
import Definitions.Def_GittinsIndex
import Theorems.Thm_SpreadBetting_Inertial_theorem_3
import Theorems.Thm_SpreadBetting_Inertial_proposition_3
import Theorems.Thm_SpreadBetting_Inertial_proposition_K_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_5
import Theorems.Thm_SpreadBetting_Inertial_proposition_2
import Theorems.Thm_SpreadBetting_Inertial_lemma_H_1

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace SBFAux
open SpreadBetting.Inertial

lemma feps_cont {M : Market} (hM : M.Standing) : Continuous M.feps :=
  hM.feps_contDiff.continuous

lemma Feps_sub {M : Market} (hM : M.Standing) (a b : ℝ) :
    Feps M b - Feps M a = ∫ t in a..b, M.feps t := by
  unfold Feps
  exact intervalIntegral.integral_Iic_sub_Iic hM.feps_integrable.integrableOn
    hM.feps_integrable.integrableOn

lemma Feps_continuous {M : Market} (hM : M.Standing) : Continuous (Feps M) := by
  have h : Feps M = fun b => Feps M 0 + ∫ t in (0:ℝ)..b, M.feps t := by
    ext b; have := Feps_sub hM 0 b; linarith
  rw [h]
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => (feps_cont hM).intervalIntegrable a b) 0)

lemma Feps_neg {M : Market} (hM : M.Standing) (x : ℝ) : Feps M x + Feps M (-x) = 1 := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (b := x) (μ := volume)
    hM.feps_integrable.integrableOn hM.feps_integrable.integrableOn
  rw [hM.feps_integral] at h1
  have h2 : ∫ t in Set.Ioi x, M.feps t = ∫ t in Set.Iic (-x), M.feps t := by
    have : ∫ t in Set.Ioi x, M.feps t = ∫ t in Set.Ioi x, M.feps (-t) := by
      congr 1; ext t; exact hM.feps_symm t
    rw [this, integral_comp_neg_Ioi]
  unfold Feps
  linarith

lemma Feps_zero {M : Market} (hM : M.Standing) : Feps M 0 = 1 / 2 := by
  have := Feps_neg hM 0
  rw [neg_zero] at this
  linarith

lemma Feps_mono {M : Market} (hM : M.Standing) {a b : ℝ} (hab : a ≤ b) :
    Feps M a ≤ Feps M b := by
  have h := Feps_sub hM a b
  have : 0 ≤ ∫ t in a..b, M.feps t :=
    intervalIntegral.integral_nonneg hab (fun t _ => hM.feps_nonneg t)
  linarith

lemma Feps_lt {M : Market} (hM : M.Standing) (a b : ℝ) (hab : a < b)
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < M.feps t) : Feps M a < Feps M b := by
  have h := Feps_sub hM a b
  have : 0 < ∫ t in a..b, M.feps t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((feps_cont hM).intervalIntegrable a b) hpos hab
  linarith

lemma F_continuous {M : Market} (hM : M.Standing) (i : Fin 2) : Continuous (F M i) := by
  unfold F
  exact (Feps_continuous hM).comp (continuous_id.sub continuous_const)

lemma F_mono {M : Market} (hM : M.Standing) (i : Fin 2) : Monotone (F M i) := by
  intro a b hab
  unfold F
  exact Feps_mono hM (by linarith)

lemma med_mem {M : Market} (i : Fin 2) : med M i = M.m0 ∨ med M i = M.m1 := by
  unfold med
  split_ifs
  · left; rfl
  · right; rfl

/-- strict increase of `F_i` to the left of any `y ∈ [m0, m1]`. -/
lemma F_lt_of_lt {M : Market} (hM : M.Standing) (i : Fin 2) {x y : ℝ}
    (hy : y ∈ Set.Icc M.m0 M.m1) (hxy : x < y) : F M i x < F M i y := by
  have h1 := hM.sL_lt_m0
  have h2 := hM.m0_lt_m1
  have hR : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
  set δ := M.m0 - M.sL with hδ
  set x' := max x (y - δ) with hx'
  have hx'y : x' < y := max_lt hxy (by linarith)
  have hle : F M i x ≤ F M i x' := F_mono hM i (le_max_left _ _)
  have hlt : F M i x' < F M i y := by
    unfold F
    apply Feps_lt hM _ _ (by linarith)
    intro t ht
    apply hM.feps_pos
    have hlo : y - δ ≤ x' := le_max_right _ _
    rw [abs_le]
    rcases med_mem (M := M) i with h | h <;> rw [h] at ht <;>
      constructor <;> linarith [ht.1, ht.2, hy.1, hy.2]
  linarith

lemma F_strictMonoOn {M : Market} (hM : M.Standing) (i : Fin 2) :
    StrictMonoOn (F M i) (Set.Icc M.m0 M.m1) :=
  fun _ _ _ hb hab => F_lt_of_lt hM i hb hab

lemma Finv_F {M : Market} (hM : M.Standing) (i : Fin 2) {y : ℝ}
    (hy : y ∈ Set.Icc M.m0 M.m1) : Finv M i (F M i y) = y := by
  unfold Finv
  apply IsLeast.csInf_eq
  refine ⟨show F M i y ≤ F M i y from le_refl _, ?_⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  have := F_lt_of_lt hM i hy hcon
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma exists_F_eq {M : Market} (hM : M.Standing) (i : Fin 2) {v : ℝ}
    (hv : v ∈ Set.Icc (F M i M.m0) (F M i M.m1)) : ∃ y ∈ Set.Icc M.m0 M.m1, F M i y = v := by
  have := intermediate_value_Icc hM.m0_lt_m1.le (F_continuous hM i).continuousOn hv
  obtain ⟨y, hy, hFy⟩ := this
  exact ⟨y, hy, hFy⟩

lemma F_Finv {M : Market} (hM : M.Standing) (i : Fin 2) {v : ℝ}
    (hv : v ∈ Set.Icc (F M i M.m0) (F M i M.m1)) :
    Finv M i v ∈ Set.Icc M.m0 M.m1 ∧ F M i (Finv M i v) = v := by
  obtain ⟨y, hy, hFy⟩ := exists_F_eq hM i hv
  rw [← hFy, Finv_F hM i hy]
  exact ⟨hy, rfl⟩

/-- reflection: `F_1(m0+m1-x) = 1 - F_0(x)`. -/
lemma F1_reflect {M : Market} (hM : M.Standing) (x : ℝ) :
    F M 1 (M.m0 + M.m1 - x) = 1 - F M 0 x := by
  unfold F med
  simp only [Fin.isValue, one_ne_zero, if_false, if_true]
  have := Feps_neg hM (x - M.m0)
  have e : M.m0 + M.m1 - x - M.m1 = -(x - M.m0) := by ring
  rw [e]
  linarith

lemma F1_m1 {M : Market} (hM : M.Standing) : F M 1 M.m1 = 1 / 2 := by
  unfold F med; simp only [Fin.isValue, one_ne_zero, if_false, sub_self]; exact Feps_zero hM

lemma F0_m0 {M : Market} (hM : M.Standing) : F M 0 M.m0 = 1 / 2 := by
  unfold F med; simp only [Fin.isValue, if_true, sub_self]; exact Feps_zero hM

lemma F0_m1 {M : Market} (hM : M.Standing) : F M 0 M.m1 = 1 - alpha M := by
  have := F1_reflect hM M.m1
  have e : M.m0 + M.m1 - M.m1 = M.m0 := by ring
  rw [e] at this
  unfold alpha
  linarith

lemma F1_m0 {M : Market} : F M 1 M.m0 = alpha M := rfl

end SBFAux
namespace SBChainConj

variable {S : Type*} [MeasurableSpace S]

/-- coordinatewise application of a measurable equivalence on finite-horizon paths -/
noncomputable def Φ (e : S ≃ᵐ S) (ι : Type*) : (ι → S) ≃ᵐ (ι → S) :=
  MeasurableEquiv.piCongrRight (fun _ : ι => e)

lemma Φ_apply (e : S ≃ᵐ S) (ι : Type*) (x : ι → S) (i : ι) : Φ e ι x i = e (x i) := rfl

lemma Φ_symm_apply (e : S ≃ᵐ S) (ι : Type*) (x : ι → S) (i : ι) :
    (Φ e ι).symm x i = e.symm (x i) := rfl

lemma step_conj (K K' : Kernel S S) [IsMarkovKernel K] [IsMarkovKernel K']
    (e : S ≃ᵐ S) (hK : ∀ x, K' (e x) = (K x).map e) (b : ℕ) :
    BanditAlgorithm.markovChainStep K' b =
      ((BanditAlgorithm.markovChainStep K b).map e).comap (Φ e (Iic b)).symm
        (Φ e (Iic b)).symm.measurable := by
  ext1 y
  simp only [BanditAlgorithm.markovChainStep, Kernel.comap_apply, Kernel.map_apply _ e.measurable]
  rw [Φ_symm_apply]
  have := hK (e.symm (y ⟨b, Finset.mem_Iic.2 le_rfl⟩))
  rw [e.apply_symm_apply] at this
  exact this


local notation "κs" => BanditAlgorithm.markovChainStep

lemma ψ_comm (e : S ≃ᵐ S) (b : ℕ) :
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b) ∘ e
      = (Φ e (Ioc b (b + 1))) ∘ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b) := by
  funext s i
  simp only [Function.comp_apply, Φ_apply]
  simp [MeasurableEquiv.piSingleton]

lemma IPI_comm (e : S ≃ᵐ S) (b : ℕ) :
    (IicProdIoc (X := fun _ : ℕ => S) b (b + 1)) ∘ (Prod.map (Φ e (Iic b)) (Φ e (Ioc b (b + 1))))
      = (Φ e (Iic (b + 1))) ∘ (IicProdIoc (X := fun _ : ℕ => S) b (b + 1)) := by
  funext x i
  simp only [Function.comp_apply, Φ_apply, IicProdIoc, Prod.map_fst, Prod.map_snd]
  split_ifs <;> rfl

lemma key_prod (K K' : Kernel S S) [IsMarkovKernel K] [IsMarkovKernel K']
    (e : S ≃ᵐ S) (hK : ∀ x, K' (e x) = (K x).map e) (b : ℕ) :
    (Kernel.id ×ₖ ((κs K' b).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b))).comap
        (Φ e (Iic b)) (Φ e (Iic b)).measurable
      = (Kernel.id ×ₖ ((κs K b).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b))).map
        (Prod.map (Φ e (Iic b)) (Φ e (Ioc b (b + 1)))) := by
  have hL : ((κs K' b).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b)).comap
        (Φ e (Iic b)) (Φ e (Iic b)).measurable
      = ((κs K b).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) b)).map
        (Φ e (Ioc b (b + 1))) := by
    ext1 y
    rw [Kernel.comap_apply, Kernel.map_apply _ (MeasurableEquiv.measurable _),
      Kernel.map_apply _ (MeasurableEquiv.measurable _),
      Kernel.map_apply _ (MeasurableEquiv.measurable _), step_conj K K' e hK b,
      Kernel.comap_apply, Kernel.map_apply _ e.measurable, Measure.map_map
        (MeasurableEquiv.measurable _) e.measurable, Measure.map_map
        (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _), ψ_comm,
      MeasurableEquiv.symm_apply_apply]
  rw [Kernel.comap_prod, hL, Kernel.id_comap, ← Kernel.id_map (Φ e (Iic b)).measurable,
    Kernel.map_prod_map _ _ (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]


lemma comp_comap' {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (η : Kernel β γ) (κ : Kernel α β) {g : δ → α} (hg : Measurable g) :
    η ∘ₖ (κ.comap g hg) = (η ∘ₖ κ).comap g hg := by
  ext1 y
  rw [Kernel.comp_apply, Kernel.comap_apply, Kernel.comap_apply, Kernel.comp_apply]

lemma partialTraj_conj (K K' : Kernel S S) [IsMarkovKernel K] [IsMarkovKernel K']
    (e : S ≃ᵐ S) (hK : ∀ x, K' (e x) = (K x).map e) (a b : ℕ) (hab : a ≤ b) :
    Kernel.partialTraj (X := fun _ : ℕ => S) (κs K') a b
      = ((Kernel.partialTraj (X := fun _ : ℕ => S) (κs K) a b).map (Φ e (Iic b))).comap
          (Φ e (Iic a)).symm (Φ e (Iic a)).symm.measurable := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
    ext1 y
    rw [Kernel.comap_apply, Kernel.map_apply _ (MeasurableEquiv.measurable _), Kernel.id_apply,
      Kernel.id_apply, Measure.map_dirac' (MeasurableEquiv.measurable _),
      MeasurableEquiv.apply_symm_apply]
  | succ b hab ih =>
    rw [Kernel.partialTraj_succ_of_le hab, Kernel.partialTraj_succ_of_le hab, ih,
      comp_comap', Kernel.comp_map _ _ (MeasurableEquiv.measurable _), key_prod K K' e hK b,
      ← Kernel.map_comp, ← Kernel.comap_map_comm]
    simp only [Kernel.map_comp]
    rw [← Kernel.map_comp_right _ ((Φ e (Iic b)).measurable.prodMap
        (Φ e (Ioc b (b + 1))).measurable) measurable_IicProdIoc,
      IPI_comm]
    have hmm : ∀ T : Kernel (Π _i : Iic b, S) ((Π _i : Iic b, S) × (Π _i : Ioc b (b + 1), S)),
        (T.map (IicProdIoc (X := fun _ : ℕ => S) b (b + 1))).map (Φ e (Iic (b + 1)))
          = T.map (⇑(Φ e (Iic (b + 1))) ∘ (IicProdIoc (X := fun _ : ℕ => S) b (b + 1))) :=
      fun T => (Kernel.map_comp_right T measurable_IicProdIoc (Φ e (Iic (b + 1))).measurable).symm
    rw [hmm]
    exact measurable_IicProdIoc


lemma traj_conj (K K' : Kernel S S) [IsMarkovKernel K] [IsMarkovKernel K']
    (e : S ≃ᵐ S) (hK : ∀ x, K' (e x) = (K x).map e) :
    Kernel.traj (X := fun _ : ℕ => S) (κs K') 0
      = ((Kernel.traj (X := fun _ : ℕ => S) (κs K) 0).map (Φ e ℕ)).comap
          (Φ e (Iic 0)).symm (Φ e (Iic 0)).symm.measurable := by
  symm
  refine Kernel.eq_traj (X := fun _ : ℕ => S) (κs K') _ (fun b => ?_)
  have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ => S) b) := by fun_prop
  have hc : (Preorder.frestrictLe (π := fun _ : ℕ => S) b) ∘ (Φ e ℕ)
      = ⇑(Φ e (Iic b)) ∘ (Preorder.frestrictLe (π := fun _ : ℕ => S) b) := by
    funext x i; rfl
  rw [← Kernel.comap_map_comm, ← Kernel.map_comp_right _ (Φ e ℕ).measurable hfr, hc,
    Kernel.map_comp_right _ hfr (Φ e (Iic b)).measurable, Kernel.traj_map_frestrictLe,
    partialTraj_conj K K' e hK 0 b (Nat.zero_le b)]
  exact hfr

theorem markovChainMeasure_conj (K K' : Kernel S S) [IsMarkovKernel K] [IsMarkovKernel K']
    (e : S ≃ᵐ S) (hK : ∀ x, K' (e x) = (K x).map e) (x : S) :
    BanditAlgorithm.markovChainMeasure K' (e x)
      = (BanditAlgorithm.markovChainMeasure K x).map (fun ω n => e (ω n)) := by
  simp only [BanditAlgorithm.markovChainMeasure, Kernel.trajMeasure]
  rw [Measure.map_dirac' (MeasurableEquiv.measurable _),
    Measure.map_dirac' (MeasurableEquiv.measurable _), Measure.dirac_bind, Measure.dirac_bind,
    traj_conj K K' e hK, Kernel.comap_apply, Kernel.map_apply _ (Φ e ℕ).measurable]
  · congr 2
    funext i
    rw [Φ_symm_apply]
    simp
  all_goals exact Kernel.measurable _

end SBChainConj

namespace SBRedAux
open SpreadBetting.Inertial SBFAux

lemma Feps_nonneg {M : Market} (hM : M.Standing) (x : ℝ) : 0 ≤ Feps M x := by
  unfold Feps
  exact setIntegral_nonneg measurableSet_Iic (fun t _ => hM.feps_nonneg t)

lemma F_mem {M : Market} (hM : M.Standing) (i : Fin 2) (x : ℝ) :
    0 ≤ F M i x ∧ F M i x ≤ 1 := by
  unfold F
  refine ⟨Feps_nonneg hM _, ?_⟩
  have := Feps_neg hM (x - med M i)
  have := Feps_nonneg hM (-(x - med M i))
  linarith

/-- the threshold `belowZbar` is a `belowWB` threshold. -/
lemma belowZbar_eq (M : Market) (ρp : ℕ → ℝ) (hne : (zbarSet M ρp).Nonempty) :
    ∃ Zb : WithBot ℤ, belowZbar M ρp = belowWB Zb := by
  by_cases hb : BddBelow (zbarSet M ρp)
  · refine ⟨((zbar M ρp : ℤ) : WithBot ℤ), ?_⟩
    funext z
    apply propext
    unfold belowZbar belowWB zbar
    rw [WithBot.coe_lt_coe]
    constructor
    · intro h
      exact h _ (Int.csInf_mem hne hb)
    · intro h w hw
      exact lt_of_lt_of_le h (csInf_le hb hw)
  · refine ⟨⊥, ?_⟩
    funext z
    apply propext
    unfold belowZbar belowWB
    rw [not_bddBelow_iff] at hb
    obtain ⟨w, hw, hwz⟩ := hb (z + 1)
    constructor
    · intro h
      have := h w hw
      omega
    · intro h
      exact absurd h (WithBot.not_lt_bot _)

lemma xiStar_eq (M : Market) (ρp : ℕ → ℝ) (Zb : WithBot ℤ)
    (h : belowZbar M ρp = belowWB Zb) (i : Fin 2) :
    xiStar M ρp i = threshStrat i (belowWB Zb) := by
  unfold xiStar; rw [h]

/-- monotonicity of `cumExp` in the reward, for a nonnegative strategy -/
lemma cumExp_mono {M : Market} (hM : M.Standing) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy)
    (hξ : ∀ h z a, 0 ≤ ξ h z a) (g1 g2 : ℤ → ℝ) (hg : ∀ z, g1 z ≤ g2 z) :
    ∀ T h z, cumExp M ρp i ξ (fun z _ _ => g1 z) T h z ≤ cumExp M ρp i ξ (fun z _ _ => g2 z) T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp]
    have hF := F_mem hM i (sTilde M ρp z)
    have hFb : 0 ≤ Fbar M i (sTilde M ρp z) := by unfold Fbar; linarith
    have a1 := ih (h ++ [(1, .pos)]) (z + 1)
    have a2 := ih (h ++ [(-1, .neg)]) (z - 1)
    have a3 := ih (h ++ [(1, .wait)]) (z + 1)
    have a4 := ih (h ++ [(-1, .wait)]) (z - 1)
    have b := hg z
    have p1 := hξ h z .pos
    have p2 := hξ h z .neg
    have p3 := hξ h z .wait
    have e1 := mul_le_mul_of_nonneg_left (add_le_add b a1) p1
    have e2 := mul_le_mul_of_nonneg_left (add_le_add b a2) p2
    have e3 := mul_le_mul_of_nonneg_left (add_le_add b a3) hFb
    have e4 := mul_le_mul_of_nonneg_left (add_le_add b a4) hF.1
    have e5 := mul_le_mul_of_nonneg_left (add_le_add e3 e4) p3
    linarith

lemma cumExp_smul (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) (ξ : Strategy) (c : ℝ) (g : ℤ → ℝ) :
    ∀ T h z, cumExp M ρp i ξ (fun z _ _ => c * g z) T h z
      = c * cumExp M ρp i ξ (fun z _ _ => g z) T h z := by
  intro T
  induction T with
  | zero => intro h z; simp [cumExp]
  | succ T ih =>
    intro h z
    simp only [cumExp, ih]
    ring

lemma xiStar_nonneg (M : Market) (ρp : ℕ → ℝ) (i : Fin 2) :
    ∀ h z a, 0 ≤ xiStar M ρp i h z a := by
  intro h z a
  unfold xiStar threshStrat
  split_ifs <;> norm_num

end SBRedAux

namespace SBRedAux2
open SpreadBetting.Inertial SBFAux SBRedAux

variable {M : Market} {ρp : ℕ → ℝ}

def P2 (M : Market) (ρp : ℕ → ℝ) : Prop :=
  ∀ z : ℤ, sTilde M ρp z ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (sTilde M ρp (-z)) = 1 / 2 + rhoExt M ρp z ∧
      F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z

lemma sTilde_neg (hM : M.Standing) (hP : P2 M ρp) (z : ℤ) :
    sTilde M ρp (-z) = M.m0 + M.m1 - sTilde M ρp z := by
  have h1 := (hP z).2.1
  have h2 := (hP z).2.2
  have hI := (hP (-z)).1
  have hI' := (hP z).1
  have hr := F1_reflect hM (sTilde M ρp (-z))
  have hmem : M.m0 + M.m1 - sTilde M ρp (-z) ∈ Set.Icc M.m0 M.m1 := by
    constructor <;> linarith [hI.1, hI.2]
  have : M.m0 + M.m1 - sTilde M ρp (-z) = sTilde M ρp z := by
    apply (F_strictMonoOn hM 1).injOn hmem hI'
    rw [hr, h1, h2]; ring
  linarith

lemma Fbar0_eq (hP : P2 M ρp) (z : ℤ) :
    Fbar M 0 (sTilde M ρp z) = F M 1 (sTilde M ρp (-z)) ∧
    F M 0 (sTilde M ρp z) = Fbar M 1 (sTilde M ρp (-z)) := by
  have h1 := (hP (-z)).2.1
  have h2 := (hP (-z)).2.2
  rw [neg_neg] at h1
  unfold Fbar
  constructor <;> linarith

lemma cumExp_reflect (hP : P2 M ρp) (below : ℤ → Prop) (g : ℤ → ℝ) :
    ∀ T h h' z, cumExp M ρp 0 (threshStrat 0 below) (fun z _ _ => g z) T h z
      = cumExp M ρp 1 (threshStrat 1 below) (fun z _ _ => g (-z)) T h' (-z) := by
  intro T
  induction T with
  | zero => intro h h' z; simp [cumExp]
  | succ T ih =>
    intro h h' z
    have i1 := ih (h ++ [(1, .wait)]) (h' ++ [(-1, .wait)]) (z + 1)
    have i2 := ih (h ++ [(-1, .wait)]) (h' ++ [(1, .wait)]) (z - 1)
    have i3 := ih (h ++ [(-1, .neg)]) (h' ++ [(1, .pos)]) (z - 1)
    rw [show -(z + 1) = -z - 1 by ring] at i1
    rw [show -(z - 1) = -z + 1 by ring] at i2 i3
    obtain ⟨f1, f2⟩ := Fbar0_eq hP z
    simp only [cumExp, threshStrat, neg_neg]
    by_cases hb : below (-z)
    · simp only [hb, if_true, Fin.isValue, zero_ne_one, if_false]
      simp only [reduceCtorEq, if_false, if_true]
      rw [i3]; ring
    · simp only [hb, if_false, Fin.isValue, zero_ne_one, if_true]
      simp only [reduceCtorEq, if_false, if_true]
      rw [i1, i2, f1, f2]; ring

lemma upProb_reflect (hM : M.Standing) (hP : P2 M ρp) (below : ℤ → Prop) (x : ℤ) :
    upProb M ρp 0 (threshStrat 0 below) (-x) = 1 - upProb M ρp 1 (threshStrat 1 below) x := by
  unfold upProb threshStrat
  simp only [neg_neg]
  by_cases hb : below x
  · simp [hb]
  · simp only [hb, neg_neg, if_false, Fin.isValue, zero_ne_one, if_true]
    simp only [reduceCtorEq, if_false, zero_add, one_mul, add_zero]
    have hF0 := F_mem hM 0 (sTilde M ρp (-x))
    have hF1 := F_mem hM 1 (sTilde M ρp x)
    have h1 := (Fbar0_eq hP (-x)).1
    rw [neg_neg] at h1
    rw [h1]
    unfold Fbar
    rw [min_eq_right hF1.2, max_eq_right hF1.1, min_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring

lemma kernel_reflect (hM : M.Standing) (hP : P2 M ρp) (below : ℤ → Prop) (x : ℤ) :
    chainKernel M ρp 0 (threshStrat 0 below) (MeasurableEquiv.neg ℤ x)
      = (chainKernel M ρp 1 (threshStrat 1 below) x).map (MeasurableEquiv.neg ℤ) := by
  have hup := upProb_reflect hM hP below x
  have hm : Measurable (MeasurableEquiv.neg ℤ) := (MeasurableEquiv.neg ℤ).measurable
  show (ENNReal.ofReal (upProb M ρp 0 (threshStrat 0 below) (-x)) • Measure.dirac (-x + 1)
      + ENNReal.ofReal (1 - upProb M ρp 0 (threshStrat 0 below) (-x)) • Measure.dirac (-x - 1))
    = (ENNReal.ofReal (upProb M ρp 1 (threshStrat 1 below) x) • Measure.dirac (x + 1)
      + ENNReal.ofReal (1 - upProb M ρp 1 (threshStrat 1 below) x) • Measure.dirac (x - 1)).map
        (MeasurableEquiv.neg ℤ)
  rw [Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul, Measure.map_dirac' hm,
    Measure.map_dirac' hm, hup]
  simp only [MeasurableEquiv.neg_apply, sub_sub_cancel]
  rw [add_comm]
  congr 2 <;> ring


lemma dist_bounds (hM : M.Standing) (hP : P2 M ρp) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ z : ℤ,
      c1 * rhoExt M ρp z ≤ |sTilde M ρp z - M.m1| ∧ |sTilde M ρp z - M.m1| ≤ c2 * rhoExt M ρp z := by
  have hm := hM.m0_lt_m1
  set I := Set.Icc (M.m0 - M.m1) 0 with hI
  have hIc : IsCompact I := isCompact_Icc
  have hIne : I.Nonempty := ⟨0, by constructor <;> linarith⟩
  have hcont := feps_cont hM
  obtain ⟨tmin, htmin, hmin⟩ := hIc.exists_isMinOn hIne hcont.continuousOn
  obtain ⟨tmax, htmax, hmax⟩ := hIc.exists_isMaxOn hIne hcont.continuousOn
  have hposI : ∀ t ∈ I, 0 < M.feps t := by
    intro t ht
    apply hM.feps_pos
    rw [abs_le]
    have h1 := hM.sL_lt_m0
    have : M.m1 - M.sL ≤ max (M.sH - M.m0) (M.m1 - M.sL) := le_max_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hfmin : 0 < M.feps tmin := hposI _ htmin
  have hfmax : 0 < M.feps tmax := hposI _ htmax
  refine ⟨1 / M.feps tmax, 1 / M.feps tmin, by positivity, by positivity, ?_⟩
  intro z
  obtain ⟨hs, -, hF1⟩ := hP z
  set s := sTilde M ρp z with hsdef
  have habs : |s - M.m1| = M.m1 - s := by
    rw [abs_of_nonpos (by linarith [hs.2])]; ring
  have hrho : rhoExt M ρp z = ∫ t in (s - M.m1)..0, M.feps t := by
    have h1 : F M 1 s = Feps M (s - M.m1) := by unfold F med; simp
    have h2 := Feps_sub hM (s - M.m1) 0
    rw [Feps_zero hM] at h2
    linarith
  have hle : s - M.m1 ≤ 0 := by linarith [hs.2]
  have hint := (hcont.intervalIntegrable (μ := volume) (s - M.m1) 0)
  have lo : ∫ t in (s - M.m1)..0, M.feps tmin ≤ ∫ t in (s - M.m1)..0, M.feps t :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const hint
      (fun t ht => hmin ⟨by linarith [ht.1, hs.1], ht.2⟩)
  have hi : ∫ t in (s - M.m1)..0, M.feps t ≤ ∫ t in (s - M.m1)..0, M.feps tmax :=
    intervalIntegral.integral_mono_on hle hint intervalIntegrable_const
      (fun t ht => hmax ⟨by linarith [ht.1, hs.1], ht.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at lo hi
  rw [habs, hrho]
  constructor
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hfmax]
    nlinarith
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hfmin]
    nlinarith

end SBRedAux2

open SpreadBetting.Inertial SBFAux SBRedAux SBRedAux2 in
theorem solution (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    -- (0) = (T3:2): z̄ ∈ ℤ ∪ {-∞}, and ξ*_i of (4.4) is a best response (2.3)
    ((zbarSet M ρp).Nonempty ∧ ∀ i : Fin 2, IsBestResponse M ρp i (xiStar M ρp i)) ∧
    -- (T4:1)
    (∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 1 (xiStar M ρp 1)) 0),
      Tendsto ω atTop atTop ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m1|) atTop (𝓝 0)) ∧
    (∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 0 (xiStar M ρp 0)) 0),
      Tendsto ω atTop atBot ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m0|) atTop (𝓝 0)) ∧
    -- (T4:2)
    (∀ i : Fin 2,
      Tendsto (fun T : ℕ => cumExp M ρp i (xiStar M ρp i)
        (fun z _ _ => |sTilde M ρp z - med M i|) T [] 0) atTop atTop ∧
      IsBigOP (fun T : ℕ => cumExp M ρp i (xiStar M ρp i)
          (fun z _ _ => |sTilde M ρp z - med M i|) T [] 0)
        (fun T : ℕ => Real.sqrt (T * Real.log T))) ∧
    -- (T4:3)
    IsBigOP (fun T : ℕ => max (regret M ρp 0 (xiStar M ρp 0) T) (regret M ρp 1 (xiStar M ρp 1) T))
      (fun T : ℕ => Real.log T) := by
  intro ρp
  obtain ⟨-, h3⟩ := theorem_3 M hM
  obtain ⟨-, hne, hbr⟩ := h3 r hr0 hr
  obtain ⟨hsv, -⟩ := lemma_H_1 M hM r hr0 hr
  have hP : P2 M ρp := (proposition_2 M hM ρp hsv.1).1
  obtain ⟨Zb, hZb⟩ := belowZbar_eq M ρp hne
  have hx1 : xiStar M ρp 1 = threshStrat 1 (belowWB Zb) := xiStar_eq M ρp Zb hZb 1
  have hx0 : xiStar M ρp 0 = threshStrat 0 (belowWB Zb) := xiStar_eq M ρp Zb hZb 0
  obtain ⟨-, hK2as, -, -⟩ := proposition_K_2 M hM ρp hsv Zb
  obtain ⟨-, ⟨hP3div, hP3O⟩, ⟨-, hP3L⟩⟩ := proposition_3 M hM r hr0 hr
  have h5 := lemma_5 M hM r hr0 hr
  -- (T4:1) under H_1
  have as1 : ∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 1 (xiStar M ρp 1)) 0),
      Tendsto ω atTop atTop ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m1|) atTop (𝓝 0) := by
    rw [hx1]; exact hK2as
  -- (T4:1) under H_0, by reflection z ↦ -z
  have as0 : ∀ᵐ ω ∂(BanditAlgorithm.markovChainMeasure (chainKernel M ρp 0 (xiStar M ρp 0)) 0),
      Tendsto ω atTop atBot ∧ Tendsto (fun t => |sTilde M ρp (ω t) - M.m0|) atTop (𝓝 0) := by
    have hconj := SBChainConj.markovChainMeasure_conj (chainKernel M ρp 1 (xiStar M ρp 1))
      (chainKernel M ρp 0 (xiStar M ρp 0)) (MeasurableEquiv.neg ℤ)
      (fun x => by rw [hx0, hx1]; exact kernel_reflect hM hP _ x) 0
    have e0 : (MeasurableEquiv.neg ℤ) 0 = 0 := by simp
    rw [e0] at hconj
    rw [hconj]
    have hemb : MeasurableEmbedding (fun (ω : ℕ → ℤ) (n : ℕ) => (MeasurableEquiv.neg ℤ) (ω n)) :=
      (SBChainConj.Φ (MeasurableEquiv.neg ℤ) ℕ).measurableEmbedding
    rw [hemb.ae_map_iff]
    filter_upwards [as1] with ω hω
    refine ⟨?_, ?_⟩
    · exact tendsto_neg_atTop_atBot.comp hω.1
    · refine hω.2.congr (fun t => ?_)
      simp only [MeasurableEquiv.neg_apply]
      rw [sTilde_neg hM hP, abs_sub_comm]
      congr 1; ring
  -- distances versus residual probabilities
  obtain ⟨c1, c2, hc1, hc2, hdist⟩ := dist_bounds hM hP
  have hξ1 := xiStar_nonneg M ρp 1
  set A : ℕ → ℝ := fun T => cumExp M ρp 1 (xiStar M ρp 1)
    (fun z _ _ => |sTilde M ρp z - M.m1|) T [] 0 with hA
  set B : ℕ → ℝ := fun T => cumExp M ρp 1 (xiStar M ρp 1)
    (fun z _ _ => rhoExt M ρp z) T [] 0 with hB
  have hAlo : ∀ T, c1 * B T ≤ A T := by
    intro T
    have := cumExp_mono hM ρp 1 (xiStar M ρp 1) hξ1 (fun z => c1 * rhoExt M ρp z)
      (fun z => |sTilde M ρp z - M.m1|) (fun z => (hdist z).1) T [] 0
    rw [cumExp_smul] at this
    exact this
  have hAhi : ∀ T, A T ≤ c2 * B T := by
    intro T
    have := cumExp_mono hM ρp 1 (xiStar M ρp 1) hξ1 (fun z => |sTilde M ρp z - M.m1|)
      (fun z => c2 * rhoExt M ρp z) (fun z => (hdist z).2) T [] 0
    rw [cumExp_smul] at this
    exact this
  have hA0 : ∀ T, 0 ≤ A T := by
    intro T
    have := cumExp_mono hM ρp 1 (xiStar M ρp 1) hξ1 (fun z => 0 * |sTilde M ρp z - M.m1|)
      (fun z => |sTilde M ρp z - M.m1|) (fun z => by simp) T [] 0
    rw [cumExp_smul, zero_mul] at this
    exact this
  have hAdiv : Tendsto A atTop atTop :=
    tendsto_atTop_mono hAlo (hP3div.const_mul_atTop hc1)
  have hAO : IsBigOP A (fun T : ℕ => Real.sqrt (T * Real.log T)) := by
    obtain ⟨C, T0, hC⟩ := hP3O
    refine ⟨c2 * C, T0, fun T hT => ?_⟩
    have h1 := hC T hT
    rw [abs_of_nonneg (hA0 T)]
    calc A T ≤ c2 * B T := hAhi T
      _ ≤ c2 * |B T| := mul_le_mul_of_nonneg_left (le_abs_self _) hc2.le
      _ ≤ c2 * (C * Real.sqrt (T * Real.log T)) := mul_le_mul_of_nonneg_left h1 hc2.le
      _ = c2 * C * Real.sqrt (T * Real.log T) := by ring
  -- the H_0 quantity equals the H_1 one by reflection
  have hA0eq : (fun T : ℕ => cumExp M ρp 0 (xiStar M ρp 0)
      (fun z _ _ => |sTilde M ρp z - M.m0|) T [] 0) = A := by
    funext T
    rw [hA]
    simp only
    rw [hx0, hx1, cumExp_reflect hP (belowWB Zb) (fun z => |sTilde M ρp z - M.m0|) T [] [] 0,
      neg_zero]
    congr 1
    funext z a d
    rw [sTilde_neg hM hP, abs_sub_comm]
    congr 1; ring
  refine ⟨⟨hne, hbr⟩, as1, as0, ?_, ?_⟩
  · intro i
    fin_cases i
    · have hmed : med M 0 = M.m0 := by unfold med; simp
      simp only [Fin.zero_eta, hmed]
      rw [hA0eq]
      exact ⟨hAdiv, hAO⟩
    · have hmed : med M 1 = M.m1 := by unfold med; simp
      simp only [Fin.mk_one, hmed]
      exact ⟨hAdiv, hAO⟩
  · obtain ⟨C, T0, hC⟩ := hP3L
    refine ⟨C, T0, fun T hT => ?_⟩
    have e : max (regret M ρp 0 (xiStar M ρp 0) T) (regret M ρp 1 (xiStar M ρp 1) T)
        = cumExp M ρp 1 (xiStar M ρp 1) (fun z _ _ => lossFn M ρp (belowZbar M ρp) z) T [] 0 :=
      (h5 T).1
    have h := hC T hT
    simp only at h ⊢
    rw [e]
    exact h
