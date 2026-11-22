-- Prove2me | solution 1 for OrderClosures.exists_solid_large_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:37.235835+00:00
-- url     : https://prove2.me/submissions/eedcb0c8-8bba-46bb-b6f8-979dd0bc71a2

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
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
public import Theorems.Thm_OrderClosures_orderAdherence_eq_solidOrderAdherence
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_Positive_le_def
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_of_monotone_isLUB
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
theorem _root_.solution (κ : Cardinal.{u}) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Lattice X) (_ : IsOrderedAddMonoid X)
      (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.aleph0 ∧
        κ ≤ solidGeneratorNumber (orderAdherence S) := by
  induction κ using Cardinal.inductionOn with
  | _ Γ =>
    let X := Option Γ → ℕ → ℝ
    let g : ℕ → X := fun n _ m ↦ if m ≤ n then (n + 1 : ℕ) else 0
    let S : Set X := solidHull (Set.range g)
    refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, S,
      LatticeOrderedAddCommGroup.isSolid_solidClosure _, ?_, ?_⟩
    · apply le_antisymm
      · calc
          solidGeneratorNumber S ≤ Cardinal.mk (Set.range g) := by
            apply csInf_le'
            exact ⟨Set.range g, rfl, rfl⟩
          _ ≤ Cardinal.aleph0 := by
            simpa [Cardinal.mk_nat] using Cardinal.mk_range_le_lift (f := g)
      · apply le_csInf
        · exact ⟨Cardinal.mk (Set.range g), Set.range g, rfl, rfl⟩
        · intro c hc
          rcases hc with ⟨A, hAc, hAS⟩
          rw [← hAc]
          by_contra hAfin
          have hAlt : Cardinal.mk A < Cardinal.aleph0 := lt_of_not_ge hAfin
          let : Finite A := Cardinal.mk_lt_aleph0_iff.mp hAlt
          have hchoice : ∀ a : A, ∃ n, |a.1| ≤ |g n| := by
            intro a
            have haS : a.1 ∈ S := by
              rw [← hAS]
              exact ⟨a.1, a.2, le_rfl⟩
            rcases haS with ⟨b, ⟨n, rfl⟩, hab⟩
            exact ⟨n, hab⟩
          choose N hN using hchoice
          obtain ⟨M, hM⟩ := Finite.exists_le N
          have hgS : g (M + 1) ∈ S := ⟨g (M + 1), ⟨M + 1, rfl⟩, le_rfl⟩
          rw [← hAS] at hgS
          rcases hgS with ⟨a, haA, hga⟩
          let aa : A := ⟨a, haA⟩
          have ha0 := hN aa (none : Option Γ) (M + 1)
          have hga0 := hga (none : Option Γ) (M + 1)
          have hNM := hM aa
          dsimp [g, X] at ha0 hga0
          rw [if_neg (by omega)] at ha0
          simp only [abs_zero] at ha0
          rw [if_pos (by omega)] at hga0
          norm_num at hga0
          change |a none (M + 1)| ≤ 0 at ha0
          have hpos : (0 : ℝ) < |(M : ℝ) + 1 + 1| := by positivity
          linarith
    · have hadh : orderAdherence S = Set.univ := by
        ext f
        simp only [Set.mem_univ, iff_true]
        have hsolid : LatticeOrderedAddCommGroup.IsSolid (orderAdherence S) := by
          rw [orderAdherence_eq_solidOrderAdherence
            (LatticeOrderedAddCommGroup.isSolid_solidClosure (Set.range g))]
          exact LatticeOrderedAddCommGroup.isSolid_solidClosure _
        apply hsolid (x := |f|) (y := f)
        · let I := ULift.{u} ℕ
          let p : I → X := fun n ↦ |f| ⊓ g n.down
          have hg_nonneg : ∀ n, 0 ≤ g n := by
            intro n γ m
            simp only [g, X]
            split_ifs <;> positivity
          have hg_mono : Monotone g := by
            intro n k hnk γ m
            simp only [g, X]
            by_cases hmn : m ≤ n
            · rw [if_pos hmn, if_pos (hmn.trans hnk)]
              exact_mod_cast Nat.succ_le_succ hnk
            · rw [if_neg hmn]
              split_ifs <;> positivity
          have hp_mono : Monotone p := fun _ _ hnk ↦
            inf_le_inf_left _ (hg_mono hnk)
          have hp_lub : IsLUB (Set.range p) |f| := by
            constructor
            · rintro _ ⟨n, rfl⟩
              exact inf_le_left
            · intro c hc γ m
              obtain ⟨k, hk⟩ := exists_nat_ge |f γ m|
              let n := max m k
              have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.le_max_right m k
              have hfn : |f γ m| ≤ (n + 1 : ℕ) := by
                norm_num
                linarith
              have hcn := hc ⟨ULift.up n, rfl⟩ γ m
              dsimp [p, g, X, n] at hcn
              rw [if_pos (Nat.le_max_left m k)] at hcn
              rw [inf_eq_left.mpr (by simpa [n] using hfn)] at hcn
              exact hcn
          refine ⟨I, inferInstance, inferInstance, inferInstance, p, ?_,
            orderConvergesTo_of_monotone_isLUB hp_mono hp_lub⟩
          intro n
          refine ⟨g n.down, ⟨n.down, rfl⟩, ?_⟩
          have hp_nonneg : 0 ≤ p n := le_inf (abs_nonneg f) (hg_nonneg n.down)
          rw [abs_of_nonneg hp_nonneg, abs_of_nonneg (hg_nonneg n.down)]
          exact (inf_le_right : |f| ⊓ g n.down ≤ g n.down)
        · simp
      rw [hadh]
      apply le_csInf
      · refine ⟨Cardinal.mk (Set.univ : Set X), Set.univ, rfl, ?_⟩
        ext x
        constructor
        · exact fun _ ↦ Set.mem_univ x
        · intro _
          exact ⟨x, Set.mem_univ x, le_rfl⟩
      · intro c hc
        rcases hc with ⟨A, hAc, hAuniv⟩
        rw [← hAc]
        by_contra hsmall
        have hlt : Cardinal.mk A < Cardinal.mk Γ := lt_of_not_ge hsmall
        obtain ⟨e⟩ := (Cardinal.le_def A Γ).mp hlt.le
        let d : Γ → ℝ := Function.extend e
          (fun a : A ↦ |a.1 (some (e a)) 0| + 1) (fun _ ↦ 0)
        let f : X := fun γ m ↦ match γ, m with
          | some δ, 0 => d δ
          | _, _ => 0
        have hfA : f ∈ solidHull A := by
          rw [hAuniv]
          exact Set.mem_univ f
        rcases hfA with ⟨a, haA, hfa⟩
        let aa : A := ⟨a, haA⟩
        have hcoord := hfa (some (e aa)) 0
        change |f (some (e aa)) 0| ≤ |a (some (e aa)) 0| at hcoord
        change |Function.extend (⇑e) (fun a : A => |a.1 (some (e a)) 0| + 1)
          (fun _ => 0) (e aa)| ≤ |a (some (e aa)) 0| at hcoord
        rw [Function.Injective.extend_apply e.injective] at hcoord
        rw [abs_of_nonneg (by positivity)] at hcoord
        linarith [abs_nonneg (a (some (e aa)) 0)]
end OrderClosures
