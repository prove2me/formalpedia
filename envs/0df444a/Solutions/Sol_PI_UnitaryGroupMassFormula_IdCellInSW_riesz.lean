-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IdCellInSW.riesz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:28:04.991889+00:00
-- url     : https://prove2.me/submissions/9a89bbba-890a-4ce2-b6db-74d92781a12f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Lemmata_GeneralBFactThirdTail_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_basis
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_dualBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable [StarRing E]
namespace PI.UnitaryGroupMassFormula.IdCellInSW
theorem _root_.solution [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (f : Λ →ₗ[𝓞 E] E) : ∃ w : V, ∀ y (hy : y ∈ Λ), h w y = f ⟨y, hy⟩ := by
  classical
  obtain ⟨s, _, b, hb, hsL⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 E) Λ hsp
  obtain ⟨d, hd, hdL⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom b Λ hΛ
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbL : ∀ i, b i ∈ Λ := fun i => by rw [hb i]; exact hsL i.2
  refine ⟨∑ k, star (f ⟨b k, hbL k⟩) • bs k, ?_⟩
  set w := ∑ k, star (f ⟨b k, hbL k⟩) • bs k with hw
  have e : ∀ j k, h (bs k) (b j) = if j = k then 1 else 0 := by
    intro j k
    rw [← hs.eq (b j) (bs k), hbs]
    split_ifs <;> simp
  have hwb : ∀ j, h w (b j) = f ⟨b j, hbL j⟩ := by
    intro j
    simp [hw, e, starRingEnd_apply, star_star]
  have hspL : Submodule.span (𝓞 E) (Set.range b) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbL j
  have hspan : ∀ u (hu : u ∈ Submodule.span (𝓞 E) (Set.range b)) (huL : u ∈ Λ),
      h w u = f ⟨u, huL⟩ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro _
      exact hwb j
    | zero =>
      intro huL
      have : (⟨0, huL⟩ : Λ) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro huL
      have e2 : (⟨x + y, huL⟩ : Λ) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e2, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro huL
      have e2 : (⟨r • x, huL⟩ : Λ) = r • ⟨x, hspL hx⟩ := rfl
      rw [e2, f.map_smul, ← algebraMap_smul E r x, (h w).map_smul, ih (hspL hx), algebraMap_smul]
  intro y hy
  have h1 := hspan (d • y) (hdL y hy) (Λ.smul_mem d hy)
  have e2 : (⟨d • y, Λ.smul_mem d hy⟩ : Λ) = d • ⟨y, hy⟩ := rfl
  rw [e2, f.map_smul, ← algebraMap_smul E d y, (h w).map_smul, ← algebraMap_smul E d (f _),
    smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1
end PI.UnitaryGroupMassFormula.IdCellInSW
