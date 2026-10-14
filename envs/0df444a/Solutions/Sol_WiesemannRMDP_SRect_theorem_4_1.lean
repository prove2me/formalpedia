-- Prove2me | solution 1 for WiesemannRMDP.SRect.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:35:38.319887+00:00
-- url     : https://prove2.me/submissions/50110e25-86a8-4bdd-b3f9-3db450e33b1b

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace RRAux_WiesemannRMDP_SRect_theorem_4_1

open FoundationsML.ReinforcementLearning Matrix WiesemannRMDP.SRect

set_option linter.unusedSectionVars false

variable {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act] {q L : ℕ}

noncomputable def F (M : Model St Act q L) (π : St → Act → ℝ) (w : St → ℝ) (ξ : Fin q → ℝ)
    (s : St) : ℝ :=
  M.rhat π ξ s + M.lam * ∑ s' : St, M.Phat π ξ s s' * w s'

lemma le_one_of_sum {ι : Type*} [Fintype ι] {f : ι → ℝ} (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∑ i, f i = 1) (i : ι) : f i ≤ 1 :=
  h1 ▸ Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma avg_le {ι : Type*} [Fintype ι] {P w : ι → ℝ} (hP : ∀ s, 0 ≤ P s) (h1 : ∑ s, P s = 1)
    {c : ℝ} (hw : ∀ s, w s ≤ c) : ∑ s, P s * w s ≤ c := by
  calc ∑ s, P s * w s ≤ ∑ s, P s * c :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hw s) (hP s)
    _ = c := by rw [← Finset.sum_mul, h1, one_mul]

lemma avg_ge {ι : Type*} [Fintype ι] {P w : ι → ℝ} (hP : ∀ s, 0 ≤ P s) (h1 : ∑ s, P s = 1)
    {c : ℝ} (hw : ∀ s, c ≤ w s) : c ≤ ∑ s, P s * w s := by
  calc c = ∑ s, P s * c := by rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ s, P s * w s :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hw s) (hP s)

lemma kern {M : Model St Act q L} (hM : M.Standing) {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) :
    IsTransitionKernel (M.pXi ξ) := hM.2.2.2.1 ξ hξ

lemma Phat_nonneg {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (s s' : St) : 0 ≤ M.Phat π ξ s s' := by
  simp only [Model.Phat, Matrix.of_apply, InducedTransition]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((kern hM hξ s a).1 s')

lemma Phat_sum {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (s : St) : ∑ s', M.Phat π ξ s s' = 1 := by
  simp only [Model.Phat, Matrix.of_apply, InducedTransition]
  rw [Finset.sum_comm]
  have hk : ∀ a, ∑ s', M.pXi ξ s a s' = 1 := fun a => (kern hM hξ s a).2
  simp only [← Finset.mul_sum, hk, mul_one]
  exact (hπ s).2

lemma rhat_nonneg {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (s : St) : 0 ≤ M.rhat π ξ s := by
  simp only [Model.rhat, InducedReward, Model.expReward]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a)
    (Finset.sum_nonneg fun s' _ => mul_nonneg ((kern hM hξ s a).1 s') (hM.2.2.2.2.1 s a s'))

lemma rhat_le {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (s : St) :
    M.rhat π ξ s ≤ ∑ a, ∑ s', M.r s a s' := by
  simp only [Model.rhat, InducedReward, Model.expReward]
  refine Finset.sum_le_sum fun a _ => ?_
  have hX : 0 ≤ ∑ s', M.pXi ξ s a s' * M.r s a s' :=
    Finset.sum_nonneg fun s' _ => mul_nonneg ((kern hM hξ s a).1 s') (hM.2.2.2.2.1 s a s')
  have hX1 : ∑ s', M.pXi ξ s a s' * M.r s a s' ≤ ∑ s', M.r s a s' :=
    Finset.sum_le_sum fun s' _ => mul_le_of_le_one_left (hM.2.2.2.2.1 s a s')
      (le_one_of_sum (kern hM hξ s a).1 (kern hM hξ s a).2 s')
  have hπ1 : π s a ≤ 1 := le_one_of_sum (hπ s).1 (hπ s).2 a
  calc π s a * ∑ s', M.pXi ξ s a s' * M.r s a s' ≤ ∑ s', M.pXi ξ s a s' * M.r s a s' :=
        mul_le_of_le_one_left hX hπ1
    _ ≤ _ := hX1

lemma lam_bound (lam x B : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (hB : 0 ≤ B) (hx : -B ≤ x)
    (hx' : x ≤ B) : -B ≤ lam * x ∧ lam * x ≤ B := by
  constructor <;> nlinarith

lemma abs_le_B (w : St → ℝ) (s : St) : |w s| ≤ ∑ s', |w s'| :=
  Finset.single_le_sum (f := fun s' => |w s'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma F_bounds {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (w : St → ℝ) (s : St) :
    -(∑ s', |w s'|) ≤ F M π w ξ s ∧ F M π w ξ s ≤ (∑ a, ∑ s', M.r s a s') + ∑ s', |w s'| := by
  have hB : 0 ≤ ∑ s', |w s'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 := avg_le (Phat_nonneg hM hπ hξ s) (Phat_sum hM hπ hξ s)
    (fun s' => (le_abs_self (w s')).trans (abs_le_B w s'))
  have h2 := avg_ge (Phat_nonneg hM hπ hξ s) (Phat_sum hM hπ hξ s)
    (fun s' => (neg_le_neg (abs_le_B w s')).trans (neg_abs_le (w s')))
  have h3 := lam_bound M.lam _ _ hM.2.2.2.2.2.1.1 hM.2.2.2.2.2.1.2 hB h2 h1
  have h4 := rhat_nonneg hM hπ hξ s
  have h5 := rhat_le hM hπ hξ s
  unfold F
  constructor <;> linarith [h3.1, h3.2]

lemma F_shift {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    {ξ : Fin q → ℝ} (hξ : ξ ∈ M.Xi) (u w : St → ℝ) (c : ℝ) (h : ∀ s', u s' ≤ w s' + c)
    (s : St) : F M π u ξ s ≤ F M π w ξ s + M.lam * c := by
  have h1 := avg_le (Phat_nonneg hM hπ hξ s) (Phat_sum hM hπ hξ s)
    (w := fun s' => u s' - w s') (c := c) (fun s' => by have := h s'; linarith)
  have h2 : ∑ s', M.Phat π ξ s s' * u s' =
      ∑ s', M.Phat π ξ s s' * w s' + ∑ s', M.Phat π ξ s s' * (u s' - w s') := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  have h3 := mul_le_mul_of_nonneg_left h1 hM.2.2.2.2.2.1.1.le
  unfold F
  rw [h2, mul_add]
  linarith

lemma iInf_le_iInf_add {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddBelow (Set.range f))
    {c : ℝ} (h : ∀ i, f i ≤ g i + c) : ⨅ i, f i ≤ (⨅ i, g i) + c := by
  have : (⨅ i, f i) - c ≤ ⨅ i, g i := le_ciInf fun i => by linarith [ciInf_le hf i, h i]
  linarith

lemma iSup_le_iSup_add {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hg : BddAbove (Set.range g))
    {c : ℝ} (h : ∀ i, f i ≤ g i + c) : ⨆ i, f i ≤ (⨆ i, g i) + c :=
  ciSup_le fun i => (h i).trans (by linarith [le_ciSup hg i])

lemma Xi_nonempty {M : Model St Act q L} (hM : M.Standing) : Nonempty M.Xi := by
  obtain ⟨ξ, hξ⟩ := hM.2.2.1
  exact ⟨⟨ξ, fun l => (hξ l).le⟩⟩

lemma pol_nonempty [Nonempty Act] : Nonempty {π : St → Act → ℝ // IsPolicy π} := by
  refine ⟨⟨fun _ _ => 1 / (Fintype.card Act : ℝ), fun s => ⟨fun a => by positivity, ?_⟩⟩⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (0 : ℝ) < Fintype.card Act := by exact_mod_cast Fintype.card_pos
  field_simp

lemma bddBelow_F {M : Model St Act q L} (hM : M.Standing) {π : St → Act → ℝ} (hπ : IsPolicy π)
    (w : St → ℝ) (s : St) : BddBelow (Set.range fun ξ : M.Xi => F M π w ξ s) :=
  ⟨-(∑ s', |w s'|), by rintro _ ⟨ξ, rfl⟩; exact (F_bounds hM hπ ξ.2 w s).1⟩

lemma bddAbove_pe {M : Model St Act q L} (hM : M.Standing) (w : St → ℝ) (s : St) :
    BddAbove (Set.range fun π : {π : St → Act → ℝ // IsPolicy π} => M.phiEval π.1 w s) := by
  haveI := Xi_nonempty hM
  obtain ⟨ξ0⟩ := ‹Nonempty M.Xi›
  refine ⟨(∑ a, ∑ s', M.r s a s') + ∑ s', |w s'|, ?_⟩
  rintro _ ⟨π, rfl⟩
  exact (ciInf_le (bddBelow_F hM π.2 w s) ξ0).trans (F_bounds hM π.2 ξ0.2 w s).2

lemma pe_eq (M : Model St Act q L) (π : St → Act → ℝ) (w : St → ℝ) (s : St) :
    M.phiEval π w s = ⨅ ξ : M.Xi, F M π w ξ s := rfl

lemma phiImprove_shift [Nonempty Act] {M : Model St Act q L} (hM : M.Standing) (u w : St → ℝ)
    (c : ℝ) (h : ∀ s', u s' ≤ w s' + c) (s : St) :
    M.phiImprove u s ≤ M.phiImprove w s + M.lam * c := by
  haveI := Xi_nonempty hM
  haveI : Nonempty {π : St → Act → ℝ // IsPolicy π} := pol_nonempty
  refine iSup_le_iSup_add (bddAbove_pe hM w s) fun π => ?_
  rw [pe_eq, pe_eq]
  exact iInf_le_iInf_add (bddBelow_F hM π.2 u s) fun ξ => F_shift hM π.2 ξ.2 u w c h s

lemma contracting [Nonempty Act] {M : Model St Act q L} (hM : M.Standing) :
    ContractingWith ⟨M.lam, hM.2.2.2.2.2.1.1.le⟩ M.phiImprove := by
  refine ⟨by exact_mod_cast hM.2.2.2.2.2.1.2, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
  have hl := hM.2.2.2.2.2.1.1.le
  show dist _ _ ≤ M.lam * dist u w
  rw [dist_pi_le_iff (mul_nonneg hl dist_nonneg)]
  intro s
  have h1 := phiImprove_shift hM u w (dist u w) (fun s' => by
    have := dist_le_pi_dist u w s'; rw [Real.dist_eq] at this
    linarith [le_abs_self (u s' - w s')]) s
  have h2 := phiImprove_shift hM w u (dist u w) (fun s' => by
    have := dist_le_pi_dist u w s'; rw [Real.dist_eq] at this
    linarith [neg_abs_le (u s' - w s')]) s
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

lemma policies_compact : IsCompact {π : St → Act → ℝ | IsPolicy π} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · show IsClosed {π : St → Act → ℝ | ∀ s, (∀ a, 0 ≤ π s a) ∧ ∑ a, π s a = 1}
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun s => (isClosed_iInter fun a => isClosed_le (by fun_prop)
      (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop))
  · refine (Metric.isBounded_closedBall (x := (0 : St → Act → ℝ)) (r := 1)).subset ?_
    intro π hπ
    rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
    intro s
    rw [dist_pi_le_iff zero_le_one]
    intro a
    rw [Pi.zero_apply, Pi.zero_apply, Real.dist_eq, sub_zero,
      abs_of_nonneg ((hπ s).1 a)]
    exact le_one_of_sum (hπ s).1 (hπ s).2 a

lemma F_cont_pi (M : Model St Act q L) (w : St → ℝ) (ξ : Fin q → ℝ) (s : St) :
    Continuous fun π : St → Act → ℝ => F M π w ξ s := by
  simp only [F, Model.rhat, InducedReward, Model.Phat, InducedTransition, Matrix.of_apply]
  fun_prop

lemma exists_max [Nonempty Act] {M : Model St Act q L} (hM : M.Standing) (w : St → ℝ) (s : St) :
    ∃ π : St → Act → ℝ, IsPolicy π ∧
      ∀ π' : St → Act → ℝ, IsPolicy π' → M.phiEval π' w s ≤ M.phiEval π w s := by
  have husc : UpperSemicontinuousOn (fun π : St → Act → ℝ => ⨅ ξ : M.Xi, F M π w ξ s)
      {π | IsPolicy π} :=
    upperSemicontinuousOn_ciInf (fun π hπ => bddBelow_F hM hπ w s)
      (fun ξ => (F_cont_pi M w ξ s).upperSemicontinuous.upperSemicontinuousOn _)
  obtain ⟨π, hπ, hmax⟩ := husc.exists_isMaxOn
    (let ⟨p⟩ := (pol_nonempty : Nonempty {π : St → Act → ℝ // IsPolicy π}); ⟨p.1, p.2⟩)
    policies_compact
  exact ⟨π, hπ, fun π' hπ' => hmax hπ'⟩

lemma glue {M : Model St Act q L} (hM : M.Standing) (hrect : M.IsSRectangular)
    (ξs : St → Fin q → ℝ) (hξs : ∀ s, ξs s ∈ M.Xi) :
    ∃ ξ ∈ M.Xi, ∀ s, M.pXi ξ s = M.pXi (ξs s) s := by
  have hP : (fun s => M.pXi (ξs s) s) ∈ M.ambiguitySet := by
    rw [hrect]
    intro s
    exact ⟨M.pXi (ξs s), ⟨kern hM (hξs s), ξs s, hξs s, rfl⟩, rfl⟩
  obtain ⟨_, ξ, hξ, hPe⟩ := hP
  exact ⟨ξ, hξ, fun s => (congrFun hPe s).symm⟩

lemma F_local (M : Model St Act q L) (π : St → Act → ℝ) (w : St → ℝ) (ξ ξ' : Fin q → ℝ)
    (s : St) (h : M.pXi ξ s = M.pXi ξ' s) : F M π w ξ s = F M π w ξ' s := by
  simp only [F, Model.rhat, InducedReward, Model.expReward, Model.Phat, InducedTransition,
    Matrix.of_apply, h]

lemma Xi_compact {M : Model St Act q L} (hM : M.Standing) : IsCompact M.Xi := by
  apply Metric.isCompact_of_isClosed_isBounded _ hM.2.1
  show IsClosed {ξ : Fin q → ℝ | ∀ l : Fin L, 0 ≤ ξ ⬝ᵥ (M.O l *ᵥ ξ) + M.o l ⬝ᵥ ξ + M.ω l}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun l => isClosed_le continuous_const ?_
  exact ((continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).add
    (continuous_const.dotProduct continuous_id)).add continuous_const

lemma small (lam m δ ε : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (hε : 0 < ε)
    (hδ : δ = ε * (1 - lam) / 2) (h : m < δ + lam * m) : m < ε := by
  subst hδ
  nlinarith

end RRAux_WiesemannRMDP_SRect_theorem_4_1

open FoundationsML.ReinforcementLearning Matrix in
open WiesemannRMDP.SRect in
open RRAux_WiesemannRMDP_SRect_theorem_4_1 in
theorem solution {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (hrect : M.IsSRectangular) :
    (∃! w : St → ℝ, M.phiImprove w = w) ∧
    ∀ wstar : St → ℝ, M.phiImprove wstar = wstar →
      (∀ s : St, ∃ π : St → Act → ℝ, IsPolicy π ∧
        ∀ π' : St → Act → ℝ, IsPolicy π' → M.phiEval π' wstar s ≤ M.phiEval π wstar s) ∧
      ∀ πs : St → St → Act → ℝ, (∀ s, IsPolicy (πs s)) →
        (∀ s, ∀ π' : St → Act → ℝ, IsPolicy π' →
          M.phiEval π' wstar s ≤ M.phiEval (πs s) wstar s) →
        IsPolicy (fun s a => πs s s a) ∧
        M.Feasible (fun s a => πs s s a) (fun _ => wstar) ∧
        M.objective (fun _ => wstar) = M.p0 ⬝ᵥ wstar ∧
        ∀ π : St → Act → ℝ, IsPolicy π → ∀ ϑ : (Fin q → ℝ) → St → ℝ,
          ContinuousOn ϑ M.Xi → M.Feasible π ϑ → M.objective ϑ ≤ M.p0 ⬝ᵥ wstar := by
  haveI := Xi_nonempty hM
  have hc := contracting hM
  refine ⟨⟨ContractingWith.fixedPoint _ hc, ContractingWith.fixedPoint_isFixedPt hc,
    fun y hy => ContractingWith.fixedPoint_unique hc hy⟩, ?_⟩
  intro wstar hfix
  refine ⟨fun s => exists_max hM wstar s, ?_⟩
  intro πs hπs hmax
  have hl0 := hM.2.2.2.2.2.1.1
  have hl1 := hM.2.2.2.2.2.1.2
  have hfix' : ∀ s, M.phiImprove wstar s = wstar s := fun s => congrFun hfix s
  have hpe_le : ∀ π, IsPolicy π → ∀ s, M.phiEval π wstar s ≤ wstar s := fun π hπ s =>
    (hfix' s) ▸ le_ciSup (bddAbove_pe hM wstar s) ⟨π, hπ⟩
  have hw_eq : ∀ s, wstar s = M.phiEval (πs s) wstar s := fun s =>
    le_antisymm ((hfix' s).symm ▸ (by
      haveI : Nonempty {π : St → Act → ℝ // IsPolicy π} := pol_nonempty
      exact ciSup_le fun π => hmax s π.1 π.2)) (hpe_le _ (hπs s) s)
  refine ⟨fun s => hπs s s, ?_, ciInf_const, ?_⟩
  · intro ξ hξ s
    have h1 : wstar s ≤ F M (πs s) wstar ξ s :=
      (hw_eq s).le.trans (ciInf_le (bddBelow_F hM (hπs s) wstar s) ⟨ξ, hξ⟩)
    exact h1
  · intro π hπ ϑ hϑc hfeas
    have hbdd : BddBelow (Set.range fun ξ : M.Xi => M.p0 ⬝ᵥ ϑ ξ) := by
      have hco : ContinuousOn (fun ξ => M.p0 ⬝ᵥ ϑ ξ) M.Xi := by
        unfold dotProduct
        exact continuousOn_finsetSum _ fun s _ =>
          continuousOn_const.mul ((continuous_apply s).comp_continuousOn hϑc)
      obtain ⟨b, hb⟩ := ((Xi_compact hM).image_of_continuousOn hco).bddBelow
      exact ⟨b, by rintro _ ⟨ξ, rfl⟩; exact hb ⟨ξ.1, ξ.2, rfl⟩⟩
    apply le_of_forall_pos_lt_add
    intro ε hε
    set δ := ε * (1 - M.lam) / 2 with hδ
    have hδpos : 0 < δ := by
      have : 0 < 1 - M.lam := by linarith
      positivity
    have hch : ∀ s, ∃ ξ : M.Xi, F M π wstar ξ s < M.phiEval π wstar s + δ := fun s =>
      exists_lt_of_ciInf_lt (by rw [pe_eq]; linarith)
    choose ξs hξs using hch
    obtain ⟨ξh, hξh, hglue⟩ := glue hM hrect (fun s => (ξs s).1) (fun s => (ξs s).2)
    have hFh : ∀ s, F M π wstar ξh s < wstar s + δ := fun s => by
      rw [F_local M π wstar ξh (ξs s).1 s (hglue s)]
      linarith [hξs s, hpe_le π hπ s]
    let g : St → ℝ := fun s => ϑ ξh s - wstar s
    obtain ⟨s0, hs0⟩ := Finite.exists_max g
    have hu : ∀ s', ϑ ξh s' ≤ wstar s' + g s0 := fun s' => by
      have := hs0 s'; simp only [g] at this ⊢; linarith
    have hsh := F_shift hM hπ hξh (ϑ ξh) wstar (g s0) hu s0
    have hf0 : ϑ ξh s0 ≤ F M π (ϑ ξh) ξh s0 := hfeas ξh hξh s0
    have hm : g s0 < δ + M.lam * g s0 := by
      have := hFh s0
      simp only [g]; linarith
    have hmε := small M.lam (g s0) δ ε hl0 hl1 hε hδ hm
    have hp0 := hM.2.2.2.2.2.2
    have hdot : M.p0 ⬝ᵥ ϑ ξh ≤ M.p0 ⬝ᵥ wstar + g s0 := by
      have h1 := avg_le (w := fun s => ϑ ξh s - wstar s) hp0.1 hp0.2 (c := g s0) hs0
      have h2 : M.p0 ⬝ᵥ ϑ ξh = M.p0 ⬝ᵥ wstar + ∑ s, M.p0 s * (ϑ ξh s - wstar s) := by
        unfold dotProduct
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      linarith
    have hobj : M.objective ϑ ≤ M.p0 ⬝ᵥ ϑ ξh := ciInf_le hbdd ⟨ξh, hξh⟩
    linarith

#print axioms solution
