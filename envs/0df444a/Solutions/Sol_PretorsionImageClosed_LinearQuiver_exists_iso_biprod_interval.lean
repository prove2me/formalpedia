-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.exists_iso_biprod_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:49.643707+00:00
-- url     : https://prove2.me/submissions/e2885449-3c19-4c62-951c-31a1bc9df577

module
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_vmap_self
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_fromVector_comp_toInterval
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_dual_eq_one
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_isZero_iff_subsingleton


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (X : Statement.LinRep k n) (hX : ¬ IsZero X) :
    ∃ (a d : Fin n) (_ : a ≤ d) (X' : Statement.LinRep k n),
      Nonempty (X ≅ interval k a d ⊞ X') := by
  classical
  -- the first nonzero vertex
  have hne : (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hX (Functor.isZero _ fun i => not_not.1 (h (Finset.mem_univ i)))
  set i₀ := (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)).min' hne with hi₀
  have hi₀_mem := Finset.min'_mem _ hne
  rw [← hi₀, Finset.mem_filter] at hi₀_mem
  have hfirst : ∀ i, i < i₀ → IsZero (X.obj i) := by
    intro i hi
    by_contra h
    have := Finset.min'_le (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)) i
      (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    rw [← hi₀] at this
    exact absurd hi (not_lt.2 this)
  -- a nonzero vector there
  have hnt : Nontrivial (X.obj i₀) := by
    rw [FGModuleCat.isZero_iff_subsingleton] at hi₀_mem
    exact not_subsingleton_iff_nontrivial.1 hi₀_mem.2
  obtain ⟨v, hv⟩ := exists_ne (0 : X.obj i₀)
  -- the last vertex to which `v` survives
  have hvi₀ : vmap X i₀ v i₀ ≠ 0 := by rw [vmap_self]; exact hv
  have hDne : (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hvi₀⟩⟩
  set d := (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0).max' hDne with hd_def
  have hd_mem := Finset.max'_mem _ hDne
  rw [← hd_def, Finset.mem_filter] at hd_mem
  have hi₀d : i₀ ≤ d := by
    have := Finset.le_max' (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0) i₀
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvi₀⟩)
    rwa [← hd_def] at this
  have hd : ∀ j, d < j → vmap X i₀ v j = 0 := by
    intro j hj
    by_contra h
    have := Finset.le_max' (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0) j
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [← hd_def] at this
    exact absurd hj (not_lt.2 this)
  -- a functional with value `1` on `X(i₀ → d)(v)`
  obtain ⟨ℓ, hℓ⟩ := exists_dual_eq_one (k := k) hd_mem.2
  -- the splitting
  haveI : IsSplitMono (fromVector d hd) :=
    ⟨⟨⟨toInterval d ℓ hfirst, fromVector_comp_toInterval d ℓ hd hfirst hℓ⟩⟩⟩
  exact ⟨i₀, d, hi₀d, cokernel (fromVector d hd), ⟨isoBiprodCokernelOfIsSplitMono (fromVector d hd)⟩⟩
end PretorsionImageClosed.LinearQuiver
