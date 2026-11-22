-- Prove2me | solution 1 for OrderClosures.leastCNFExponent_chain_lub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:58.727263+00:00
-- url     : https://prove2.me/submissions/8c782969-6134-4466-a2d0-5cf66271b588

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Theorems.Thm_OrderClosures_cnf_singleton_spec
public import Theorems.Thm_OrderClosures_cnf_eq_singleton_of_isLUB
public import Theorems.Thm_OrderClosures_CNFListLT_eq_dropLast_of_length_eq
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_CNF_cnfValue
public import Theorems.Thm_OrderClosures_CNF_cnfValue_add_monomial
public import Theorems.Thm_OrderClosures_cnfAddMonomial_lastExponent
public import Theorems.Thm_OrderClosures_cnfExtensionLE_partialOrder_and_subrelation
public import Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
public import Theorems.Thm_OrderClosures_cnfValue_append
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom


section
@[expose] public section
namespace OrderClosures
open Set
universe u v
section OrdinalConstruction
private theorem exists_chain_CNF_prefix
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (ζ : GaoIndex ξ)
    (hchain : ∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
      cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1)
    (habove : ∃ η : GaoIndex ξ, η ∈ Z ∧ ζ.1 < η.1) :
    ∃ η₀ ∈ Z, ζ.1 < η₀.1 ∧ ∃ pre : List (Ordinal.{u} × Ordinal.{u}),
      ∀ η ∈ Z, η₀.1 ≤ η.1 → ∃ δ d,
        Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] := by
  classical
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := habove
  obtain ⟨η₀, hη₀U, hη₀min⟩ := exists_minimalFor_of_wellFoundedLT U
    (fun η : GaoIndex ξ ↦ (Ordinal.CNF Ordinal.omega0 η.1).length) hU
  have hη₀Z : η₀ ∈ Z := hη₀U.1
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀Z, le_rfl⟩
  have hrelV : ∀ η ∈ V, cnfExtensionLE η₀.1 η.1 := by
    intro η hηV
    rcases hchain hη₀Z hηV.1 with h | h
    · exact h
    · exact Or.inl (le_antisymm hηV.2
        (cnfExtensionLE_partialOrder_and_subrelation.2 h))
  have hlenV : ∀ η ∈ V,
      (Ordinal.CNF Ordinal.omega0 η.1).length =
        (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · rw [heq]
    · have hle : (Ordinal.CNF Ordinal.omega0 η.1).length ≤
          (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
        rcases cnfExtensionLT_iff_CNFListLT.mp hlt with
          ⟨pre, tail, x, y, hη₀cnf, hηcnf, _⟩
        rw [hη₀cnf, hηcnf]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      exact le_antisymm hle
        (hη₀min ⟨hηV.1, hη₀U.2.trans_le hηV.2⟩ hle)
  let pre := (Ordinal.CNF Ordinal.omega0 η₀.1).dropLast
  have hη₀ne : Ordinal.CNF Ordinal.omega0 η₀.1 ≠ [] := by
    have hη₀pos : 0 < η₀.1 :=
      (zero_le : (0 : Ordinal) ≤ ζ.1).trans_lt hη₀U.2
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 η₀.1
    rw [h] at hfold
    exact hη₀pos.ne' hfold.symm
  have hcnfV : ∀ η ∈ V, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · have hsub : η₀ = η := Subtype.ext heq
      subst η
      let p := (Ordinal.CNF Ordinal.omega0 η₀.1).getLast hη₀ne
      refine ⟨p.1, p.2, ?_⟩
      simpa only [pre, p] using (List.dropLast_append_getLast hη₀ne).symm
    · obtain ⟨x, y, _, hηcnf, _⟩ :=
        CNFListLT.eq_dropLast_of_length_eq
          (cnfExtensionLT_iff_CNFListLT.mp hlt) (hlenV η hηV)
      exact ⟨y.1, y.2, hηcnf⟩
  exact ⟨η₀, hη₀Z, hη₀U.2, pre, fun η hηZ hle => hcnfV η ⟨hηZ, hle⟩⟩
private theorem cnf_residual_of_common_prefix {η : Ordinal.{u}}
    (pre : List (Ordinal.{u} × Ordinal.{u})) (δ d : Ordinal.{u})
    (hηcnf : Ordinal.CNF Ordinal.omega0 η = pre ++ [(δ, d)]) :
    Ordinal.CNF Ordinal.omega0 (η - cnfValue pre) = [(δ, d)] ∧
      cnfValue pre + (η - cnfValue pre) = η := by
  have hηeq : (cnfValue pre) + cnfValue [(δ, d)] = η := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 η]
    change (cnfValue pre) + cnfValue [(δ, d)] = cnfValue (Ordinal.CNF Ordinal.omega0 η)
    rw [hηcnf, cnfValue_append]
  have hρle : (cnfValue pre) ≤ η := hηeq ▸ le_self_add
  have hsub : η - (cnfValue pre) = cnfValue [(δ, d)] :=
    Ordinal.sub_eq_of_add_eq hηeq
  constructor
  · rw [hsub]
    apply CNF_cnfValue
    · simp
    · intro p hp
      exact Ordinal.CNF.snd_pos (by
        rw [hηcnf]
        exact List.mem_append_right _ hp)
    · intro p hp
      exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
        rw [hηcnf]
        exact List.mem_append_right _ hp)
  · exact Ordinal.add_sub_cancel_of_le hρle
private theorem chain_subtraction_isLUB
    {ξ : Ordinal.{u}} {Z : Set (GaoIndex ξ)} {α η₀ : GaoIndex ξ} (ρ : Ordinal.{u})
    (hchain : ∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
      cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1)
    (hsup : IsLUB ((fun η : GaoIndex ξ ↦ η.1) '' Z) α.1) (hη₀Z : η₀ ∈ Z)
    (hrecover : ∀ η ∈ Z, η₀.1 ≤ η.1 → ρ + (η.1 - ρ) = η.1) :
    IsLUB ((fun η : GaoIndex ξ ↦ η.1 - ρ) '' {η | η ∈ Z ∧ η₀.1 ≤ η.1})
      (α.1 - ρ) := by
  have hρaddη₀ := hrecover η₀ hη₀Z le_rfl
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hρleα := hρleη₀.trans (hsup.1 ⟨η₀, hη₀Z, rfl⟩)
  have hρadda : ρ + (α.1 - ρ) = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  constructor
  · rintro _ ⟨η, hηV, rfl⟩
    rw [Ordinal.sub_le, hρadda]
    exact hsup.1 ⟨η, hηV.1, rfl⟩
  · intro b hb
    rw [Ordinal.sub_le]
    apply hsup.2
    rintro _ ⟨η, hηZ, rfl⟩
    rcases hchain hηZ hη₀Z with hηη₀ | hη₀η
    · calc
        η.1 ≤ η₀.1 := cnfExtensionLE_partialOrder_and_subrelation.2 hηη₀
        _ = ρ + (η₀.1 - ρ) := hρaddη₀.symm
        _ ≤ ρ + b := add_le_add_right (hb ⟨η₀, ⟨hη₀Z, le_rfl⟩, rfl⟩) ρ
    · have hle := cnfExtensionLE_partialOrder_and_subrelation.2 hη₀η
      calc
        η.1 = ρ + (η.1 - ρ) := (hrecover η hηZ hle).symm
        _ ≤ ρ + b := add_le_add_right (hb ⟨η, ⟨hηZ, hle⟩, rfl⟩) ρ
end OrdinalConstruction
end OrderClosures
end
end

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1)
    (hleast : ∀ ζ ∈ Z, leastCNFExponent ζ.1 < γ) :
    leastCNFExponent α.1 ≤ γ := by
  classical
  by_cases hαZ : α ∈ Z
  · exact (hleast α hαZ).le
  obtain ⟨ζ, hζZ⟩ := hne
  have hζα : ζ.1 < α.1 := (hsup.1 ⟨ζ, hζZ, rfl⟩).lt_of_ne fun h ↦ by
    have hsub : ζ = α := Subtype.ext h
    exact hαZ (hsub ▸ hζZ)
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := by
    by_contra h
    have hαζ : α.1 ≤ ζ.1 := hsup.2 (by
      rintro _ ⟨η, hηZ, rfl⟩
      exact le_of_not_gt fun hζη ↦ h ⟨η, hηZ, hζη⟩)
    exact (not_le_of_gt hζα) hαζ
  obtain ⟨η₀, hη₀Z, _hζη₀_lt, pre, hcommon⟩ :=
    exists_chain_CNF_prefix ξ Z ζ hchain hU
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀Z, le_rfl⟩
  have hcnfV : ∀ η ∈ V, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] :=
    fun η hηV => hcommon η hηV.1 hηV.2
  let ρ : Ordinal.{u} := cnfValue pre
  have residual_of_common : ∀ (η : GaoIndex ξ) (δ d : Ordinal.{u}),
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] →
      Ordinal.CNF Ordinal.omega0 (η.1 - ρ) = [(δ, d)] ∧
        ρ + (η.1 - ρ) = η.1 := by
    intro η δ d hηcnf
    exact cnf_residual_of_common_prefix pre δ d hηcnf
  let Q : Set (Ordinal.{u}) := (fun η : GaoIndex ξ ↦ η.1 - ρ) '' V
  have hQne : Q.Nonempty := ⟨η₀.1 - ρ, ⟨η₀, hη₀V, rfl⟩⟩
  have hsingleQ : ∀ q ∈ Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ := by
    rintro q ⟨η, hηV, rfl⟩
    obtain ⟨δ, d, hηcnf⟩ := hcnfV η hηV
    refine ⟨δ, d, (residual_of_common η δ d hηcnf).1, ?_⟩
    have := hleast η hηV.1
    simpa [leastCNFExponent, hηcnf] using this
  obtain ⟨δ₀, d₀, hη₀cnf⟩ := hcnfV η₀ hη₀V
  have hρaddη₀ := (residual_of_common η₀ δ₀ d₀ hη₀cnf).2
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hρleα : ρ ≤ α.1 := hρleη₀.trans (hsup.1 ⟨η₀, hη₀Z, rfl⟩)
  let a : Ordinal.{u} := α.1 - ρ
  have hρadda : ρ + a = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  have hlubQ : IsLUB Q a := by
    apply chain_subtraction_isLUB ρ hchain hsup hη₀Z
    intro η hηZ hle
    obtain ⟨δ, d, hηcnf⟩ := hcnfV η ⟨hηZ, hle⟩
    exact (residual_of_common η δ d hηcnf).2
  obtain ⟨Γ, D, hacnf⟩ := cnf_eq_singleton_of_isLUB Q a hQne
    (fun q hq ↦ let ⟨δ, d, h, _⟩ := hsingleQ q hq; ⟨δ, d, h⟩) hlubQ
  have hpowUpper : Ordinal.omega0 ^ γ ∈ upperBounds Q := by
    intro q hq
    obtain ⟨δ, d, hqcnf, hδγ⟩ := hsingleQ q hq
    obtain ⟨_, _, _, hlogq⟩ := cnf_singleton_spec hqcnf
    exact ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
      obtain ⟨hqeq, hdpos, _, _⟩ := cnf_singleton_spec hqcnf
      rw [hqeq]
      exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
        hdpos.ne')).2 (by simpa only [hlogq] using hδγ)).le
  have haPow : a ≤ Ordinal.omega0 ^ γ := hlubQ.2 hpowUpper
  obtain ⟨haeq, hDpos, _, _⟩ := cnf_singleton_spec hacnf
  have hΓγ : Γ ≤ γ := by
    rw [haeq] at haPow
    have hΓa : Ordinal.omega0 ^ Γ ≤ Ordinal.omega0 ^ Γ * D :=
      Ordinal.le_mul_left _ hDpos
    exact (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp
      (hΓa.trans haPow)
  have hsortedPre : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 η₀.1).pairwise
    rw [hη₀cnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hposPre : ∀ p ∈ pre, 0 < p.2 := by
    intro p hp
    exact Ordinal.CNF.snd_pos (by rw [hη₀cnf]; exact List.mem_append_left _ hp)
  have hltPre : ∀ p ∈ pre, p.2 < Ordinal.omega0 := by
    intro p hp
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hη₀cnf]
      exact List.mem_append_left _ hp)
  have hαcnf : Ordinal.CNF Ordinal.omega0 α.1 = cnfAddMonomial pre Γ D := by
    rw [← hρadda, haeq]
    exact CNF_cnfValue_add_monomial pre hsortedPre hposPre hltPre Γ D hDpos
      (cnf_singleton_spec hacnf).2.2.1
  rw [leastCNFExponent, hαcnf, cnfAddMonomial_lastExponent]
  exact hΓγ
end OrderClosures
