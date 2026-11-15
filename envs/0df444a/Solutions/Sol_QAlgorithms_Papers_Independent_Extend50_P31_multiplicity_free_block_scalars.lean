-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.multiplicity_free_block_scalars
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:26:33.954976+00:00
-- url     : https://prove2.me/submissions/baa9a315-940d-44c7-ac65-e1368d3ec469

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A] {n : ℕ}
private def bundled (U : UnitaryIrrep G n) : Representation ℂ G (Fin n → ℂ) where
  toFun g := (U.rho g).mulVecLin
  map_one' := by ext v i; simp [U.one]
  map_mul' g h := by ext v i; simp [U.mul, Matrix.mulVec_mulVec]

private lemma bundled_irred (U : UnitaryIrrep G n) : Representation.IsIrreducible (bundled U) := by
  have hn : Nonempty (Fin n) := ⟨⟨0, U.positive⟩⟩
  letI := hn
  have hne : (⊥ : Subrepresentation (bundled U)) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases U.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G A : Type*} [Group G] [Fintype G] [DecidableEq A] (F : IrrepFamily G A) (theta : Finset A)
    (M : ((a : {a // a ∈ theta}) → Fin (F.dim a.val) → ℂ) →ₗ[ℂ]
      ((a : {a // a ∈ theta}) → Fin (F.dim a.val) → ℂ))
    (hM : ∀ g v a, M (fun b => ((F.irrep b.val).rho g).mulVec (v b)) a =
      ((F.irrep a.val).rho g).mulVec (M v a)) :
    ∃ l : {a // a ∈ theta} → ℂ, ∀ v a, M v a = l a • v a := by
  classical
  let V := fun a : {a // a ∈ theta} => Fin (F.dim a.val) → ℂ
  let f (a b : {a // a ∈ theta}) :
      Representation.IntertwiningMap (bundled (F.irrep b.val)) (bundled (F.irrep a.val)) :=
    { toLinearMap := (LinearMap.proj a).comp (M.comp (LinearMap.single ℂ V b))
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        change M (Pi.single b (((F.irrep b.val).rho g).mulVec x)) a =
          ((F.irrep a.val).rho g).mulVec (M (Pi.single b x) a)
        have he : (Pi.single b (((F.irrep b.val).rho g).mulVec x) : ∀ a, V a) =
            fun c => ((F.irrep c.val).rho g).mulVec ((Pi.single b x : ∀ a, V a) c) := by
          funext c
          by_cases h : c = b
          · subst c; simp
          · simp [Pi.single_apply,h]
        rw [he]
        exact hM g (Pi.single b x) a }
  have hoff (a b : {a // a ∈ theta}) (hab : a ≠ b) : f a b = 0 := by
    letI := bundled_irred (F.irrep a.val)
    letI := bundled_irred (F.irrep b.val)
    rcases Representation.IsIrreducible.bijective_or_eq_zero (f a b) with hb | hz
    · have e := (f a b).ofBijective hb
      have he : b.val = a.val := F.inequivalent b.val a.val
        ⟨e.toLinearEquiv,fun g v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v⟩
      exact False.elim (hab (Subtype.ext he.symm))
    · exact hz
  have hdiag (a : {a // a ∈ theta}) : ∃ c : ℂ,
      algebraMap ℂ (Representation.IntertwiningMap (bundled (F.irrep a.val)) (bundled (F.irrep a.val))) c = f a a := by
    letI := bundled_irred (F.irrep a.val)
    exact Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 (f a a)
  choose l hl using hdiag
  refine ⟨l,?_⟩
  intro v a
  have hv : (∑ b : {a // a ∈ theta}, Pi.single b (v b)) = v := LinearMap.sum_single_apply V v
  calc
    M v a = M (∑ b : {a // a ∈ theta}, Pi.single b (v b)) a := congrArg (fun w => M w a) hv.symm
    _ = ∑ b : {a // a ∈ theta}, M (Pi.single b (v b)) a := by simp only [map_sum,Finset.sum_apply]
    _ = ∑ b : {a // a ∈ theta}, if b = a then l a • v a else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      change (f a b) (v b) = _
      by_cases hab : b = a
      · subst b
        simp only [if_pos rfl]
        have hh := congrArg (fun q : Representation.IntertwiningMap (bundled (F.irrep a.val)) (bundled (F.irrep a.val)) => q (v a)) (hl a)
        simpa [Representation.IntertwiningMap.algebraMap_apply] using hh.symm
      · rw [hoff a b (Ne.symm hab)]
        simp [hab]
    _ = l a • v a := by simp