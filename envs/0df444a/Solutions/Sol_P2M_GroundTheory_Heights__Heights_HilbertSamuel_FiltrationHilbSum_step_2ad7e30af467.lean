-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:01.092803+00:00
-- url     : https://prove2.me/submissions/7ca3c484-914b-42d9-b295-be4f31bcf51e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_form_smul_mem_50a6c960c889
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_apply_c807c9273bfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_smul_f065e44fd581
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finiteDimensional_piece_458f90289b82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_proof_9860939069fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedPieceQuot_proof_ce5357543371


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
open Classical
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
theorem _root_.solution [∀ k, Fintype (ι k)] (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {N N' : Submodule (MRing ι F) M} {x : M} {c : K → ℤ} {q : Ideal (MRing ι F)}
    (hx : x ∈ piece c) (hN' : N' = N ⊔ Submodule.span (MRing ι F) {x})
    (hq : ∀ s : MRing ι F, s • x ∈ N ↔ s ∈ q)
    (hgr : ∀ y ∈ N, ∀ m, comp (piece := piece) m y ∈ N) (m : K → ℤ)
    [FiniteDimensional F ↥(N.restrictScalars F ⊓ piece m)] :
    FiniteDimensional F ↥(N'.restrictScalars F ⊓ piece m) ∧
      (Module.finrank F ↥(N'.restrictScalars F ⊓ piece m) : ℤ) =
        Module.finrank F ↥(N.restrictScalars F ⊓ piece m) + hilbFn q (m - c) := by
  set A := N.restrictScalars F ⊓ piece m with hA
  have hNN' : N ≤ N' := hN' ▸ le_sup_left
  have hAB : A ≤ N'.restrictScalars F ⊓ piece m := inf_le_inf_right _ hNN'
  have hdec : ∀ y ∈ N'.restrictScalars F ⊓ piece m, ∃ n ∈ A, ∃ s : MRing ι F,
      y = n + comp (piece := piece) m (s • x) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.restrictScalars_mem, hN'] at hy1
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨comp (piece := piece) m n, Submodule.mem_inf.mpr ⟨hgr n hn m, ?_⟩, s, ?_⟩
    · rw [comp_apply]
      exact Submodule.coe_mem _
    · have h := DirectSum.decompose_of_mem_same piece hy2
      rw [← comp_apply] at h
      rw [← map_add, h]
  by_cases hb : ∀ k, 0 ≤ (m - c) k
  · set b : K → ℕ := fun k => ((m - c) k).toNat with hbdef
    have hbm : m = c + fun k => (b k : ℤ) := by
      funext k
      have := hb k
      simp only [Pi.sub_apply] at this
      simp only [hbdef, Pi.add_apply, Pi.sub_apply]
      omega
    let ψ : MRing ι F →ₗ[F] M := (LinearMap.toSpanSingleton (MRing ι F) M x).restrictScalars F
    have hψ : ∀ s, ψ s = s • x := fun s => rfl
    set P := weightedHomogeneousSubmodule F (blockWeight ι) b with hP
    set Q := P ⊓ q.restrictScalars F with hQ
    have hPm : ∀ s ∈ P, s • x ∈ piece m := by
      intro s hs
      have h := form_smul_mem hM hs hx
      rwa [← hbm] at h
    have hsup : N'.restrictScalars F ⊓ piece m = A ⊔ P.map ψ := by
      apply le_antisymm
      · intro y hy
        obtain ⟨n, hn, s, rfl⟩ := hdec y hy
        refine Submodule.add_mem_sup hn ⟨weightedHomogeneousComponent (blockWeight ι) b s,
          weightedHomogeneousComponent_mem _ s b, ?_⟩
        rw [hψ, comp_smul hM hx, weightedHomogeneousComponent_apply]
        congr 1
        refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
        have h2 : ∀ k, 0 ≤ m k - c k := fun k => by simpa using hb k
        constructor
        · intro h
          funext k
          show ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k
          rw [h, hbdef]
          simp only [Pi.sub_apply]
          have := h2 k
          omega
        · intro h
          funext k
          have h1 : ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k := by
            simpa using congrFun h k
          rw [hbdef]
          show Finsupp.weight (blockWeight ι) d k = ((m - c) k).toNat
          rw [Pi.sub_apply]
          omega
      · refine sup_le hAB ?_
        rintro _ ⟨s, hs, rfl⟩
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · rw [Submodule.restrictScalars_mem, hψ, hN']
          exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
        · exact hPm s hs
    have hinf : A ⊓ P.map ψ = Q.map ψ := by
      apply le_antisymm
      · rintro _ ⟨hA', ⟨s, hs, rfl⟩⟩
        refine ⟨s, Submodule.mem_inf.mpr ⟨hs, ?_⟩, rfl⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ]
        exact (Submodule.mem_inf.mp hA').1
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ⟨s, hs1, rfl⟩⟩
        · rw [Submodule.restrictScalars_mem, hψ, hq]
          exact hs2
        · rw [hψ]
          exact hPm s hs1
    have : FiniteDimensional F P := FiltrationStepHilb.finiteDimensional_piece b
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq A (P.map ψ)
    have k1 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict P)
    have k2 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict Q)
    rw [LinearMap.range_domRestrict] at k1 k2
    have hker : ∀ R : Submodule F (MRing ι F), Module.finrank F ↥(LinearMap.ker (ψ.domRestrict R)) =
        Module.finrank F ↥(R ⊓ LinearMap.ker ψ) := by
      intro R
      rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    have hPQ : P ⊓ LinearMap.ker ψ = Q ⊓ LinearMap.ker ψ := by
      apply le_antisymm
      · intro s hs
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hs1, ?_⟩, hs2⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ, LinearMap.mem_ker.mp hs2]
        exact N.zero_mem
      · exact inf_le_inf_right _ inf_le_left
    rw [hker, hPQ] at k1
    rw [hker] at k2
    have hq' := GradedPieceQuot.proof F K ι q b
    have hhilb : hilbFn q (m - c) = (Module.finrank F ↥(gradedPiece q b) : ℤ) := by
      unfold hilbFn
      rw [if_pos hb]
    rw [hsup, hinf] at *
    refine ⟨inferInstance, ?_⟩
    have key : (Module.finrank F ↥(A ⊔ P.map ψ) : ℤ) =
        Module.finrank F A + (Module.finrank F P - Module.finrank F Q) := by
      have k1' : Module.finrank F ↥(P.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F P := k1
      have k2' : Module.finrank F ↥(Q.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F Q := k2
      have e1' : Module.finrank F ↥(A ⊔ P.map ψ) + Module.finrank F ↥(Q.map ψ) =
          Module.finrank F A + Module.finrank F ↥(P.map ψ) := e1
      clear k1 k2 e1 hq' hhilb
      omega
    rw [hhilb, hq', key]
  · have hsup : N'.restrictScalars F ⊓ piece m = A := by
      refine le_antisymm (fun y hy => ?_) hAB
      obtain ⟨n, hn, s, rfl⟩ := hdec y hy
      rw [comp_smul hM hx, Finset.filter_false_of_mem, Finset.sum_empty, zero_smul, add_zero]
      · exact hn
      · intro d _ h
        refine hb fun k => ?_
        rw [← h]
        exact Int.natCast_nonneg _
    have hhilb : hilbFn q (m - c) = 0 := by
      unfold hilbFn
      rw [if_neg hb]
    rw [hsup, hhilb, add_zero]
    exact ⟨inferInstance, rfl⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
