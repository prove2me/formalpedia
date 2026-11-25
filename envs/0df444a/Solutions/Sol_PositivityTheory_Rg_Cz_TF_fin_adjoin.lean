-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.fin_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:25.499347+00:00
-- url     : https://prove2.me/submissions/cf999a49-454a-445a-a3f8-dded9d6354cc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_monic_lprod
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Finite ι] (x : ι → A)
    (hc : ∀ i j, Commute (x i) (x j)) (hL : ∀ i, ∃ L : List ℂ, (L.map fun c => x i - algebraMap ℂ A c).prod = 0) :
    FiniteDimensional ℂ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range x))) := by
  classical
  have hcomm : ∀ a ∈ Set.range x, ∀ b ∈ Set.range x, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j
  letI : CommRing (Algebra.adjoin ℂ (Set.range x)) := Algebra.adjoinCommRingOfComm ℂ hcomm
  have hint : ∀ i, IsIntegral ℂ (x i) := by
    intro i
    obtain ⟨L, hL⟩ := hL i
    refine ⟨(L.map fun c => Polynomial.X - Polynomial.C c).prod, monic_lprod L, ?_⟩
    rw [← Polynomial.aeval_def, map_list_prod, List.map_map]
    have hf : (⇑(Polynomial.aeval (x i)) ∘ fun c => Polynomial.X - Polynomial.C c) =
        fun c => x i - algebraMap ℂ A c := by
      funext c
      simp [Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hf]
    exact hL
  let y : ι → Algebra.adjoin ℂ (Set.range x) := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hyint : ∀ z ∈ Set.range y, IsIntegral ℂ z := by
    rintro _ ⟨i, rfl⟩
    exact (isIntegral_algHom_iff (Algebra.adjoin ℂ (Set.range x)).val Subtype.val_injective).1 (hint i)
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range y) hyint
  have hset : Set.range y = Subtype.val ⁻¹' (Set.range x) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have htop : Algebra.adjoin ℂ (Set.range y) = ⊤ := by
    rw [hset]
    exact Algebra.adjoin_adjoin_coe_preimage
  rw [htop] at hfin
  have hS : Module.Finite ℂ (Algebra.adjoin ℂ (Set.range x)) :=
    Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv
  exact Subalgebra.finiteDimensional_toSubmodule.2 hS
end PositivityTheory.Rg.Cz.TF
