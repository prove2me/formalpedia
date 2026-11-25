-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho__bdb24f9c611b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:39.006304+00:00
-- url     : https://prove2.me/submissions/65799448-e2bd-4fb4-b86e-9cb28cf854eb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {I : Submodule (𝓞 K) V} {I' : Submodule (𝓞 K) V'} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I (n + 1)) (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    ∃ S : VecSplit h h', h S.x₀ S.x₀ = 1 ∧ S.adjoin I' = I := by
  obtain ⟨e, hli, hspan, hIe, horth⟩ := hI
  obtain ⟨e', hli', hspan', hIe', horth'⟩ := hI'
  have hsucc : LinearIndependent K (fun j : Fin n => e j.succ) := hli.comp _ (Fin.succ_injective n)
  let b' : Basis (Fin n) K V' := Basis.mk hli' hspan'.ge
  let bs : Basis (Fin n) K (Submodule.span K (Set.range fun j : Fin n => e j.succ)) := Basis.span hsucc
  let ι : V' →ₗ[K] V := (Submodule.subtype _).comp (b'.equiv bs (Equiv.refl _)).toLinearMap
  have hιe : ∀ j, ι (e' j) = e j.succ := by
    intro j
    have h1 : e' j = b' j := (Basis.mk_apply hli' hspan'.ge j).symm
    rw [h1]
    simp only [ι, bs, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply, Basis.span_apply]
  have hinj : Function.Injective ι := Subtype.val_injective.comp (LinearEquiv.injective _)
  let b : Basis (Fin (n + 1)) K V := Basis.mk hli hspan.ge
  have hisom : ∀ a c, h (ι a) (ι c) = h' a c := by
    have hB : (h.comp ι).compl₂ ι = h' := by
      refine LinearMap.ext_basis b' b' (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, b', Basis.mk_apply, hιe, horth, horth',
        Fin.succ_inj]
    intro a c
    exact congrArg (fun B : V' →ₗ⋆[K] V' →ₗ[K] K => B a c) hB
  have horthι : ∀ a, h (e 0) (ι a) = 0 := by
    have hz : (h (e 0)).comp ι = 0 := by
      refine b'.ext (fun j => ?_)
      simp [b', hιe, horth, (Fin.succ_ne_zero j).symm]
    intro a
    exact LinearMap.congr_fun hz a
  have hcover : ∀ v, ∃ (c : K) (a : V'), v = c • e 0 + ι a := by
    intro v
    refine ⟨b.repr v 0, ∑ j : Fin n, b.repr v j.succ • e' j, ?_⟩
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_succ, map_sum]
    simp only [b, Basis.mk_apply, map_smul, hιe]
  refine ⟨⟨e 0, ι, hinj, ?_, hisom, horthι, hcover⟩, ?_, ?_⟩
  · rw [horth 0 0]
    simp
  · show h (e 0) (e 0) = 1
    rw [horth 0 0]
    simp
  · show Submodule.span (𝓞 K) {e 0} ⊔ I'.map (ι.restrictScalars (𝓞 K)) = I
    rw [hIe', hIe, Submodule.map_span]
    have hr : Set.range e = insert (e 0) (Set.range fun j : Fin n => e j.succ) := by
      ext v
      simp only [Set.mem_range, Set.mem_insert_iff]
      rw [Fin.exists_fin_succ]
      exact or_congr_left eq_comm
    rw [hr, Submodule.span_insert]
    congr 2
    ext v
    simp [hιe]
end Formalism.HermitianLattices.Ext.L3
