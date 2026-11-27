-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Orth.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:20.349961+00:00
-- url     : https://prove2.me/submissions/265ac321-223f-4edb-869a-e73f5c6480de

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_OrthogonalDecomposition_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Orth
variable {H P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
namespace PositivityTheory.ThKEnd.Orth
theorem _root_.solution (ρ : H → Module.End ℂ P) (c : H → Module.End ℂ Q) [Nontrivial P]
    (irr : ∀ N : Submodule ℂ P, (∀ h, ∀ x ∈ N, ρ h x ∈ N) → N = ⊥ ∨ N = ⊤) (R : Submodule ℂ Q) (hR : ∀ h, ∀ x ∈ R, c h x ∈ R)
    {f : Q} (hf : f ∈ R) (hs : f ∈ Submodule.span ℂ (vals ρ c)) :
    ∃ (m : ℕ) (U : Fin m → P →ₗ[ℂ] Q) (ξ : Fin m → P), (∀ i, (∀ h x, U i (ρ h x) = c h (U i x)) ∧ ∀ x, U i x ∈ R) ∧
      f = ∑ i, U i (ξ i) := by
  classical
  let A := FreeAlgebra ℂ H
  letI : Module A P := Module.compHom P (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module A Q := Module.compHom Q (FreeAlgebra.lift ℂ c).toRingHom
  have eP : ∀ (a : A) (x : P), a • x = FreeAlgebra.lift ℂ ρ a x := fun _ _ => rfl
  have eQ : ∀ (a : A) (x : Q), a • x = FreeAlgebra.lift ℂ c a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A P := ⟨fun z a x => by rw [eP, eP, map_smul]; rfl⟩
  haveI : IsScalarTower ℂ A Q := ⟨fun z a x => by rw [eQ, eQ, map_smul]; rfl⟩
  haveI : IsSimpleModule A P := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases irr (N.restrictScalars ℂ) (fun h x hx => by
      simpa [eP] using N.smul_mem (FreeAlgebra.ι ℂ h) hx) with h | h
    · exact Or.inl (Submodule.restrictScalars_injective ℂ A P h)
    · exact Or.inr (Submodule.restrictScalars_injective ℂ A P h)
  let R' : Submodule A Q :=
    { R.toAddSubmonoid with
      smul_mem' := fun a x hx => by
        induction a using FreeAlgebra.induction generalizing x with
        | grade0 z => simpa [eQ] using R.smul_mem z hx
        | grade1 h => simpa [eQ] using hR h x hx
        | mul a b ha hb => rw [mul_smul]; exact ha _ (hb _ hx)
        | add a b ha hb => rw [add_smul]; exact R.add_mem (ha _ hx) (hb _ hx) }
  obtain ⟨m, z, g, rfl⟩ := Submodule.mem_span_set'.1 hs
  choose U hU x hx using fun i => (g i).2
  let V : Fin m → P →ₗ[A] Q := fun i =>
    { (U i).toAddHom with
      map_smul' := fun a y => by
        change U i (a • y) = a • U i y
        induction a using FreeAlgebra.induction generalizing y with
        | grade0 z => simp [eP, eQ]
        | grade1 h => simpa [eP, eQ] using hU i h y
        | mul a b ha hb => rw [mul_smul, mul_smul, ha, hb]
        | add a b ha hb => rw [add_smul, add_smul, map_add, ha, hb] }
  let T : (Fin m → P) →ₗ[A] Q := ∑ i, V i ∘ₗ LinearMap.proj i
  have hT : T (fun i => z i • x i) = ∑ i, z i • (g i : Q) := by
    simp only [T, LinearMap.sum_apply, hx, ← map_smul]
    rfl
  obtain ⟨C, hC⟩ := exists_isCompl (R'.comap T)
  let π := (R'.comap T).subtype ∘ₗ Submodule.linearProjOfIsCompl _ C hC
  refine ⟨m, fun i => (T ∘ₗ π ∘ₗ LinearMap.single A (fun _ => P) i).restrictScalars ℂ, fun i => z i • x i,
    fun i => ⟨fun h y => ?_, fun y => Subtype.prop (p := (· ∈ R'.comap T)) _⟩, ?_⟩
  · simpa [eP, eQ] using (T ∘ₗ π ∘ₗ LinearMap.single A (fun _ => P) i).map_smul (FreeAlgebra.ι ℂ h) y
  · have e : π (fun i => z i • x i) = fun i => z i • x i :=
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨_, show T _ ∈ R from hT ▸ hf⟩)
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, ← map_sum, LinearMap.single_apply, Finset.univ_sum_single]
    exact hT.symm.trans (congrArg T e.symm)
end PositivityTheory.ThKEnd.Orth
