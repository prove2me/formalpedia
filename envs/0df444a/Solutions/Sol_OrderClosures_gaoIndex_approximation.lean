-- Prove2me | solution 1 for OrderClosures.gaoIndex_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:06.08603+00:00
-- url     : https://prove2.me/submissions/cd636a3a-d18c-420b-9516-843ad1a56112

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Theorems.Thm_OrderClosures_singletonCNFBelow_isLUB
public import Theorems.Thm_OrderClosures_singletonCNF_step_of_lt
public import Theorems.Thm_OrderClosures_cnfValue_add_singleton_below
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



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) (ζ : GaoIndex ξ)
    (hζbound : ζ.1 ≤ Ordinal.omega0 ^ ξ)
    (hζleast : leastCNFExponent ζ.1 = γ) :
    ∃ Z : Set (GaoIndex ξ), Z.Nonempty ∧
      (∀ η ∈ Z, η ∈ GaoStageIndices ξ γ) ∧
      (∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
        cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1) ∧
      IsLUB ((fun η : GaoIndex ξ ↦ η.1) '' Z) ζ.1 := by
  classical
  have hζ0 : ζ.1 ≠ 0 := by
    intro hzero
    have : γ = 0 := by
      rw [← hζleast, hzero]
      simp [leastCNFExponent]
    exact hγ this
  let pre := (Ordinal.CNF Ordinal.omega0 ζ.1).dropLast
  have hcnfne : Ordinal.CNF Ordinal.omega0 ζ.1 ≠ [] := by
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 ζ.1
    rw [h] at hfold
    exact hζ0 hfold.symm
  let p := (Ordinal.CNF Ordinal.omega0 ζ.1).getLast hcnfne
  have hpcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [p] := by
    simpa only [pre, p] using (List.dropLast_append_getLast hcnfne).symm
  have hpγ : p.1 = γ := by
    have := hζleast
    rw [leastCNFExponent, hpcnf] at this
    have hlast : (pre ++ [p]).getLast? = some p := by simp
    rw [hlast] at this
    simpa using this
  let c := p.2
  have hpeq : p = (γ, c) := Prod.ext hpγ rfl
  have hζcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [(γ, c)] := by
    rw [hpcnf, hpeq]
  have hcpos : 0 < c := by
    apply Ordinal.CNF.snd_pos (x := (γ, c))
    rw [hζcnf]
    simp
  have hclt : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (x := (γ, c))
    rw [hζcnf]
    simp
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hclt
  have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let ρ : Ordinal.{u} := cnfValue pre
  let base : Ordinal.{u} := ρ + Ordinal.omega0 ^ γ * (n : Ordinal)
  have hζeq : ζ.1 = base + Ordinal.omega0 ^ γ := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ.1, hζcnf, hm]
    change cnfValue (pre ++ [(γ, ((n + 1 : ℕ) : Ordinal))]) =
      base + Ordinal.omega0 ^ γ
    rw [cnfValue_append]
    simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
    dsimp [base, ρ]
    change cnfValue pre + Ordinal.omega0 ^ γ * ((n + 1 : ℕ) : Ordinal) =
      cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + Ordinal.omega0 ^ γ
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
  let Q := singletonCNFBelow γ
  have hQne : Q.Nonempty := by
    have hγpos : 0 < γ := (pos_iff_ne_zero).2 hγ
    have honepow : (1 : Ordinal) < Ordinal.omega0 ^ γ := by
      have hp : Ordinal.omega0 ^ (1 : Ordinal) ≤ Ordinal.omega0 ^ γ :=
        (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).2
          (by simpa using (Order.succ_le_iff.2 hγpos : Order.succ 0 ≤ γ))
      exact Ordinal.one_lt_omega0.trans_le (by simpa using hp)
    refine ⟨1, 0, 1, ?_, honepow⟩
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := 0) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos 0 Ordinal.omega0_pos)
  let ηval : Q → Ordinal.{u} := fun q ↦ base + q.1
  have hηlt : ∀ q : Q, ηval q < ζ.1 := by
    intro q
    obtain ⟨δ, d, hqcnf, hqpow⟩ := q.2
    rw [hζeq]
    exact (add_lt_add_iff_left base).2 hqpow
  let η : Q → GaoIndex ξ := fun q ↦
    ⟨ηval q, (hηlt q).le.trans hζbound |>.trans le_self_add⟩
  have hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hpreAbove : ∀ x ∈ pre, γ < x.1 := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    intro x hx
    exact h.2.2 x.1 (by exact List.mem_map.mpr ⟨x, hx, rfl⟩)
      γ (by simp)
  have hprePos : ∀ x ∈ pre, 0 < x.2 := by
    intro x hx
    exact Ordinal.CNF.snd_pos (by rw [hζcnf]; exact List.mem_append_left _ hx)
  have hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0 := by
    intro x hx
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hζcnf]
      exact List.mem_append_left _ hx)
  have hηcnf : ∀ q : Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q.1 = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0 (η q).1 =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by
    intro q
    exact cnfValue_add_singleton_below pre γ n hpreSorted hpreAbove hprePos hpreLt q.1 q.2
  have hηstage : ∀ q : Q, η q ∈ GaoStageIndices ξ γ := by
    intro q
    obtain ⟨δ, d, hqcnf, hδγ, hcnf⟩ := hηcnf q
    refine ⟨(hηlt q).le.trans hζbound, ?_⟩
    rw [leastCNFExponent, hcnf]
    split_ifs <;> simp_all
  let Z : Set (GaoIndex ξ) := Set.range η
  let : Nonempty Q := hQne.to_subtype
  have hZne : Z.Nonempty := Set.range_nonempty η
  have hZstage : ∀ η' ∈ Z, η' ∈ GaoStageIndices ξ γ := by
    rintro _ ⟨q, rfl⟩
    exact hηstage q
  have hηchainLT : ∀ q r : Q, q.1 < r.1 →
      cnfExtensionLT (η q).1 (η r).1 := by
    intro q r hqr
    obtain ⟨δ, d, hqcnf, hδγ, hqηcnf⟩ := hηcnf q
    obtain ⟨ε, e, hrcnf, hεγ, hrηcnf⟩ := hηcnf r
    have hstep := singletonCNF_step_of_lt hqcnf hrcnf hqr
    by_cases hn : n = 0
    · refine ⟨pre, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn] using hqηcnf
      · simpa [hn] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, by
            by_cases hp : pre = []
            · exact Or.inl hp
            · let last := pre.getLast hp
              have hlast : pre.getLast? = some last := by
                dsimp [last]
                exact List.getLast?_eq_getLast_of_ne_nil hp
              have hlastMem : last ∈ pre := by
                dsimp [last]
                exact List.getLast_mem hp
              exact Or.inr ⟨last.1, last.2, hlast,
                hεγ.trans (hpreAbove last hlastMem)⟩⟩
    · let common := pre ++ [(γ, (n : Ordinal))]
      refine ⟨common, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn, common, List.append_assoc] using hqηcnf
      · simpa [hn, common, List.append_assoc] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, Or.inr ⟨γ, (n : Ordinal), by
            simp [common], hεγ⟩⟩
  have hZchain : ∀ ⦃η₁⦄, η₁ ∈ Z → ∀ ⦃η₂⦄, η₂ ∈ Z →
      cnfExtensionLE η₁.1 η₂.1 ∨ cnfExtensionLE η₂.1 η₁.1 := by
    rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩
    rcases lt_trichotomy q.1 r.1 with hlt | heq | hgt
    · exact Or.inl (Or.inr (hηchainLT q r hlt))
    · have hsub : q = r := Subtype.ext heq
      subst r
      exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr (hηchainLT r q hgt))
  have hvalLUB : IsLUB ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) ζ.1 := by
    have hmap := (Ordinal.isNormal_add_right base).map_isLUB
      (singletonCNFBelow_isLUB γ hγ) hQne
    rw [hζeq]
    have hsets : ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) =
        (fun q : Ordinal.{u} ↦ base + q) '' Q := by
      ext x
      constructor
      · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
        exact ⟨q.1, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨η ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    rw [hsets]
    exact hmap
  exact ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩
end OrderClosures
