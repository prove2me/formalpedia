-- Prove2me | solution 1 for P2M_GlobalTheory_LocMod_Inhab_exists_map_wave__4bfad06d87ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:25.2064+00:00
-- url     : https://prove2.me/submissions/c179c19e-1f39-4418-9c4b-bb1198106364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
import Theorems.Thm_GlobalTheory_PlaceModel_linearIndependent_wave
import Theorems.Thm_GlobalTheory_PlaceModel_wave_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) {L L' : AddSubgroup G}
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hY : ∀ y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', σ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, ∀ x y, T (wave χ L x y) = ρ x (σ y f₀) := by
  have hli := linearIndependent_wave (X := ⊤) (Y := ⊤) (L := L) (L' := L') h fun y _ => hY y
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Module.Basis.span hli).constr ℂ
    fun i => ρ (i.1.out : (⊤ : AddSubgroup G)) (σ (i.2.out : (⊤ : AddSubgroup G)) f₀))
  have hT' : ∀ i : ((⊤ : AddSubgroup G) ⧸ L.addSubgroupOf ⊤) × ((⊤ : AddSubgroup G) ⧸ L'.addSubgroupOf ⊤),
      T (wave χ L (i.1.out : (⊤ : AddSubgroup G)) (i.2.out : (⊤ : AddSubgroup G))) =
        ρ (i.1.out : (⊤ : AddSubgroup G)) (σ (i.2.out : (⊤ : AddSubgroup G)) f₀) := fun i => by
    have := LinearMap.congr_fun hT (Module.Basis.span hli i)
    rw [Module.Basis.constr_basis] at this
    simpa using this
  refine ⟨T, fun x y => ?_⟩
  let p : (⊤ : AddSubgroup G) ⧸ L.addSubgroupOf ⊤ := QuotientAddGroup.mk ⟨x, trivial⟩
  let q : (⊤ : AddSubgroup G) ⧸ L'.addSubgroupOf ⊤ := QuotientAddGroup.mk ⟨y, trivial⟩
  have hp : -((p.out : (⊤ : AddSubgroup G)) : G) + x ∈ L :=
    (QuotientAddGroup.eq (s := L.addSubgroupOf ⊤) (a := p.out) (b := ⟨x, trivial⟩)).1 p.out_eq'
  have hq : -((q.out : (⊤ : AddSubgroup G)) : G) + y ∈ L' :=
    (QuotientAddGroup.eq (s := L'.addSubgroupOf ⊤) (a := q.out) (b := ⟨y, trivial⟩)).1 q.out_eq'
  have := hT' (p, q)
  simp only at this
  generalize ((p.out : (⊤ : AddSubgroup G)) : G) = x0 at *
  generalize ((q.out : (⊤ : AddSubgroup G)) : G) = y0 at *
  have ex : x = x0 + (-x0 + x) := by abel
  have ey : y = y0 + (-y0 + y) := by abel
  generalize -x0 + x = l at *
  generalize -y0 + y = l' at *
  rw [ex, ey, wave_add h hLL' _ _ hp hq, map_smul, this, ← hρ, ← hσ, hf' _ hq, hc l, hf _ hp, map_smul]
end GlobalTheory.LocMod.Inhab
