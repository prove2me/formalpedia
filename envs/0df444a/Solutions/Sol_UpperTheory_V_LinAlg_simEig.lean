-- Prove2me | solution 1 for UpperTheory.V.LinAlg.simEig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:53.247804+00:00
-- url     : https://prove2.me/submissions/6f342ac8-41f1-435e-91d2-38a11c419306

import Mathlib
import Definitions.Def_Development_WeilBound_SimpleEigenvalues_SimpleEigenvalueExtension_SimEig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.V.LinAlg
theorem _root_.solution :
    ∀ {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
        {J : Type} (T : J → Module.End K M), (∀ i j : J, T i * T j = T j * T i) →
        ∀ (d : ℕ) (U : Submodule K M), Module.finrank K U = d → U ≠ ⊥ → (∀ j : J, ∀ x ∈ U, T j x ∈ U) →
        ∃ v ∈ U, v ≠ 0 ∧ ∀ j : J, ∃ c : K, T j v = c • v := by
  intro K M _ _ _ _ _ J T hT _ U _ hU hst
  let A : Subalgebra K (Module.End K M) := Algebra.adjoin K (Set.range T)
  have hA : ∀ a ∈ A, (∀ x ∈ U, a x ∈ U) ∧ ∀ j, a * T j = T j * a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h => obtain ⟨i, rfl⟩ := h; exact ⟨hst i, hT i⟩
    | algebraMap r => exact ⟨fun x hx => U.smul_mem r hx, fun j => Algebra.commutes r _⟩
    | add a b _ _ ha hb =>
      exact ⟨fun x hx => U.add_mem (ha.1 x hx) (hb.1 x hx),
        fun j => by rw [add_mul, mul_add, ha.2, hb.2]⟩
    | mul a b _ _ ha hb =>
      exact ⟨fun x hx => ha.1 _ (hb.1 x hx),
        fun j => by rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]⟩
  let U' : Submodule A M :=
    { carrier := U
      add_mem' := fun hx hy => U.add_mem hx hy
      zero_mem' := U.zero_mem
      smul_mem' := fun a x hx => (hA a.1 a.2).1 x hx }
  have hU' : U' ≠ ⊥ := by
    intro h
    apply hU
    rw [Submodule.eq_bot_iff] at h ⊢
    exact h
  haveI : IsArtinian A M := isArtinian_of_tower K inferInstance
  obtain ⟨S, hS, hSU⟩ := (eq_bot_or_exists_atom_le U').resolve_left hU'
  haveI : IsSimpleModule A S := isSimpleModule_iff_isAtom.2 hS
  haveI : FiniteDimensional K S :=
    FiniteDimensional.of_injective (S.subtype.restrictScalars K) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
  refine ⟨v, hSU hv, hv0, fun j => ?_⟩
  let t : A := ⟨T j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  let f : Module.End A S :=
    { toFun := fun x => t • x
      map_add' := fun x y => smul_add t x y
      map_smul' := fun a x => by
        apply Subtype.ext
        exact (LinearMap.congr_fun ((hA a.1 a.2).2 j) (x : M)).symm }
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := A) (V := S)).2 f
  refine ⟨c, ?_⟩
  have h := congrArg Subtype.val (LinearMap.congr_fun hc ⟨v, hv⟩)
  exact h.symm
end UpperTheory.V.LinAlg
