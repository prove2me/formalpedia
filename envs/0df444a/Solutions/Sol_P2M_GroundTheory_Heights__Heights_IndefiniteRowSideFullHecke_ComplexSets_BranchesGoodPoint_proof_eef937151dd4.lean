-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchesGoodPoint_proof_eef937151dd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:02.473207+00:00
-- url     : https://prove2.me/submissions/f2f5a739-28b9-43f2-bd86-8459d099e597

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOneComponentGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchesGoodPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix
noncomputable section
private theorem mem_zeroSet_sup_linForm {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {u x : Fin n → ℂ}
    (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (hu : GroundTheory.Heights₂.Heights.linEval u x = 0) :
    x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (J ⊔ Ideal.span {linForm u}) := by
  have hle : J ⊔ Ideal.span {linForm u} ≤ RingHom.ker (eval x) := by
    refine sup_le (fun g hg => RingHom.mem_ker.2 (hx g hg)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simpa [linForm, GroundTheory.Heights₂.Heights.linEval] using hu
  exact fun g hg => RingHom.mem_ker.1 (hle hg)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace BranchesGoodPoint
theorem _root_.solution (hP : GeneralProjection.Statement)
    (hO : OneComponentGeneralPoint.Statement) (hI : SliceImmersiveGeneral.Statement)
    (hB : BranchProperAtPoint.Statement) : BranchesGoodPoint.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj _
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨N₂, hN₂, hsl₂⟩ := hsl
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp ⟨N₂, hN₂, hsl₂⟩
  obtain ⟨U, hUo, hUd, hUg⟩ := hO n _ W hW
  set O := interior (N₁ ∩ N₂ ∩ V) with hOdef
  have hOp : O ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem (inter_mem hN₁ hN₂) hV)

  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) O hOp
  have hyV : y ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := ⟨hyW, (interior_subset hyO).2⟩
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd hyV) (O ∩ U)
    (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∩ N₂ ∩ V ∈ 𝓝 q := mem_interior_iff_mem_nhds.1 hqO
  choose s hs hs0 hsq hsinj using hqs

  set L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b =>
    (fderiv ℂ (γ b).toFun (s b) : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
      ((Fin.consEquivL ℂ (fun _ : Fin (d + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ
        LinearMap.inr ℂ ℂ (Fin d → ℂ)) with hLdef
  have hLapp : ∀ b w, L b w = fderiv ℂ (γ b).toFun (s b) (Fin.cons 0 w) := fun b w => rfl
  have hL : ∀ b, Function.Injective (L b) := by
    intro b
    refine (injective_iff_map_eq_zero (L b)).2 fun w hw => ?_
    rw [hLapp] at hw
    have h0 := hsinj b (Fin.cons 0 w) (by simp) hw
    funext i
    simpa using congrFun h0 i.succ
  obtain ⟨π, hπ⟩ := hP n d m L hL
  refine ⟨q, π, s, hqW, ⟨N₁, mem_of_superset hqN fun x hx => hx.1.1, hcov₁⟩,
    ⟨N₂, mem_of_superset hqN fun x hx => hx.1.2, hsl₂⟩, ?_, fun b => ⟨hs b, hs0 b, hsq b⟩, ?_, ?_⟩
  · obtain ⟨N, hN, hNW⟩ := hUg q ⟨hqW, hqU⟩
    exact ⟨N, hN, fun x hx hux => hNW ⟨mem_zeroSet_sup_linForm hx.1 hux, hx.2⟩⟩
  · intro b
    have hd : DifferentiableAt ℂ (γ b).toFun (s b) :=
      (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))
    set πL : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ) := (Matrix.mulVecLin π).toContinuousLinearMap
    set Φ : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
      (Fin.consEquivL ℂ (fun _ : Fin (d + 1) => ℂ) : _ →L[ℂ] _) ∘L
        ((ContinuousLinearMap.proj 0).prod (πL ∘L fderiv ℂ (γ b).toFun (s b))) with hΦdef
    have h1 : HasFDerivAt (fun τ : Fin (d + 1) → ℂ => ((τ 0, πL ((γ b).toFun τ)) : ℂ × (Fin d → ℂ)))
        ((ContinuousLinearMap.proj 0).prod (πL ∘L fderiv ℂ (γ b).toFun (s b))) (s b) :=
      (hasFDerivAt_apply 0 (s b)).prodMk (πL.hasFDerivAt.comp (s b) hd.hasFDerivAt)
    have hF : HasFDerivAt (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) Φ (s b) :=
      (Fin.consEquivL ℂ (fun _ : Fin (d + 1) => ℂ)).hasFDerivAt.comp (s b) h1
    rw [hF.fderiv]
    have hinj : Function.Injective Φ := by
      refine (injective_iff_map_eq_zero Φ).2 fun v hv => ?_
      have hv' : ((v 0, πL (fderiv ℂ (γ b).toFun (s b) v)) : ℂ × (Fin d → ℂ)) = 0 :=
        (Fin.consEquivL ℂ (fun _ : Fin (d + 1) => ℂ)).injective (by simpa [hΦdef] using hv)
      have hv0 : v 0 = 0 := congrArg Prod.fst hv'
      have hvc : v = Fin.cons 0 (Fin.tail v) := by rw [← hv0, Fin.cons_self_tail]
      have hw : π *ᵥ L b (Fin.tail v) = π *ᵥ L b 0 := by
        rw [map_zero, Matrix.mulVec_zero, hLapp, ← hvc]
        exact congrArg Prod.snd hv'
      rw [hvc, hπ b hw]
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (Φ : (Fin (d + 1) → ℂ) →ₗ[ℂ] _))).1 hinj⟩
  · exact fun b => hB n (d + 1) J u p q m γ hJ hdim hu
      ⟨N₁, mem_of_superset hqN fun x hx => hx.1.1, hcov₁⟩ hdisj b (s b) (hs b) (hsq b)
end BranchesGoodPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
