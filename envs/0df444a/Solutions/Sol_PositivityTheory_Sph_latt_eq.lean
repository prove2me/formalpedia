-- Prove2me | solution 1 for PositivityTheory.Sph.latt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:06.79191+00:00
-- url     : https://prove2.me/submissions/e936f4fc-0a9e-4f4f-a863-47abde410691

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LattEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.Sph
theorem _root_.solution {n d : ℕ} {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ v : Fin d → k, v ∈ latt t Y₀ ↔ ∀ j, (v ᵥ* h.1) j ∈ 𝒪[k] := by
  classical
  set L := latt t Y₀ with hL
  have : Module.Finite 𝒪[k] L := by
    rw [hL, latt]
    exact Module.Finite.span_of_finite _ ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := 𝒪[k]) (M := L)
  set w : Fin m → (Fin d → k) := fun i => (b i : Fin d → k) with hw
  have hwL : ∀ i, w i ∈ L := fun i => (b i).2
  have hli : LinearIndependent k w := by
    rw [← LinearIndependent.iff_fractionRing 𝒪[k] k]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hsum : ∀ x (hx : x ∈ L), x = ∑ i, ((b.repr ⟨x, hx⟩ i : 𝒪[k]) : k) • w i := by
    intro x hx
    have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    refine e.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact (algebraMap_smul k _ _).symm
  have hLw : ∀ x ∈ L, x ∈ Submodule.span k (Set.range w) := by
    intro x hx
    rw [hsum x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span k (Set.range w) := by
    intro x _
    have hx : x = ∑ j, (t⁻¹ * x j) • (t • Pi.single j (1 : k) : Fin d → k) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLw _ ?_)
    exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  let bk := Module.Basis.mk hli hsp
  have hbk : ∀ i, bk i = w i := fun i => by simp [bk]
  have hm : m = d := by
    have := Module.finrank_eq_card_basis bk
    simpa using this.symm
  have hmem : ∀ v, v ∈ L ↔ ∀ i, bk.equivFun v i ∈ 𝒪[k] := by
    intro v
    constructor
    · intro hv i
      have : bk.equivFun v = fun i => ((b.repr ⟨v, hv⟩ i : 𝒪[k]) : k) := by
        apply bk.equivFun.symm.injective
        rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
        simpa only [hbk] using hsum v hv
      rw [this]
      exact (b.repr _ i).2
    · intro hc
      rw [← bk.sum_equivFun v]
      refine L.sum_mem fun i _ => ?_
      rw [hbk i, show bk.equivFun v i • w i = (⟨bk.equivFun v i, hc i⟩ : 𝒪[k]) • w i from rfl]
      exact L.smul_mem _ (hwL i)
  let bk' := bk.reindex (finCongr hm)
  let hmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.toLinearMap)ᵀ
  let Bmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.symm.toLinearMap)ᵀ
  have hB : hmat * Bmat = 1 := by
    simp only [hmat, Bmat, ← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨hmat, Bmat, hB, mul_eq_one_comm.mp hB⟩, fun v => ?_⟩
  have key : v ᵥ* hmat = bk'.equivFun v := by
    simp [hmat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hre : ∀ j, bk'.equivFun v j = bk.equivFun v ((finCongr hm).symm j) := by
    intro j
    simp [bk', Module.Basis.equivFun_apply]
  show v ∈ L ↔ ∀ j, (v ᵥ* hmat) j ∈ 𝒪[k]
  rw [key, hmem]
  simp only [hre]
  exact ⟨fun H j => H _, fun H i => by simpa using H (finCongr hm i)⟩
end PositivityTheory.Sph
