-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.dex_block_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:47.176498+00:00
-- url     : https://prove2.me/submissions/8935c2f7-9933-472b-8d9c-8243a0d8a909

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_Normal
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexBlockFrame
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module
variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (I : Ideal R) [I.IsMaximal] {L : Type} [Fintype L] (b : Basis L k (R ⧸ I))
    {W : Type} [AddCommGroup W] [Module R W] [Module k W] [IsScalarTower k R W] [FiniteDimensional k W]
    (hW : ∀ z ∈ I, ∀ y : W, z • y = 0) (N : W →ₗ[R] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (β : Basis (L × Σ a : ι, Fin (l a)) k W),
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧
      (∀ (z : R) (p : L) (j : Σ a : ι, Fin (l a)),
        z • β (p, j) = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • β (q, j)) ∧
      (∀ (p : L) (a : ι) (i : Fin (l a)), N (β (p, ⟨a, i⟩)) =
        if h : (i : ℕ) + 1 < l a then β (p, ⟨a, ⟨i + 1, h⟩⟩) else 0) ∧
      v = ∑ p, ∑ a, (if h : s a < l a then b.repr 1 p • β (p, ⟨a, ⟨s a, h⟩⟩) else 0) ∧
      ∀ A : W →ₗ[R] W, A ∘ₗ N = N ∘ₗ A → ∀ (p : L) (a : ι) (i : Fin (l a)), (i : ℕ) < s a →
        β.repr (A v) (p, ⟨a, i⟩) = 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hT : Module.IsTorsionBySet R W I := fun y z => hW z z.2 y
  letI : Module (R ⧸ I) W := hT.module
  have hmk : ∀ (z : R) (y : W), (Ideal.Quotient.mk I z) • y = z • y := fun z y => rfl
  haveI : IsScalarTower k (R ⧸ I) W := ⟨fun c e y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective e
    have : c • Ideal.Quotient.mk I z = Ideal.Quotient.mk I (c • z) := (map_smul (Ideal.Quotient.mkₐ k I) c z).symm
    rw [this, hmk, hmk, smul_assoc]⟩
  haveI : FiniteDimensional (R ⧸ I) W := Module.Finite.of_restrictScalars_finite k (R ⧸ I) W
  let toE : (W →ₗ[R] W) → (W →ₗ[R ⧸ I] W) := fun f =>
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.id_apply, hmk]
        exact f.map_smul z y }
  have htoE : ∀ f y, toE f y = f y := fun f y => rfl
  have hNE : IsNilpotent (toE N) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun y => ?_⟩
    have : ((toE N) ^ m) y = (N ^ m) y := by
      rw [Module.End.pow_apply, Module.End.pow_apply]
      rfl
    rw [this, hm]
    rfl
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hv, hA⟩ := exists_normal (toE N) hNE v
  refine ⟨ι, inferInstance, l, s, b.smulTower B, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z p j
    rw [Basis.smulTower_apply]
    calc z • (b p • B j) = (Ideal.Quotient.mk I z) • (b p • B j) := rfl
      _ = (Ideal.Quotient.mk I z * b p) • B j := by rw [smul_smul]
      _ = (∑ q, b.repr (Ideal.Quotient.mk I z * b p) q • b q) • B j := by rw [b.sum_repr]
      _ = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • (b.smulTower B) (q, j) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Basis.smulTower_apply, smul_assoc]
  · intro p a i
    rw [Basis.smulTower_apply]
    have h1 : N (b p • B ⟨a, i⟩) = b p • (toE N) (B ⟨a, i⟩) := (toE N).map_smul (b p) (B ⟨a, i⟩)
    rw [h1, hB a i]
    split_ifs with h
    · rw [Basis.smulTower_apply]
    · rw [smul_zero]
  · rw [Finset.sum_comm]
    conv_lhs => rw [hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : s a < l a
    · simp only [h, dif_pos, Basis.smulTower_apply]
      calc B ⟨a, ⟨s a, h⟩⟩ = (1 : R ⧸ I) • B ⟨a, ⟨s a, h⟩⟩ := (one_smul _ _).symm
        _ = (∑ p, b.repr 1 p • b p) • B ⟨a, ⟨s a, h⟩⟩ := by rw [b.sum_repr]
        _ = ∑ p, b.repr 1 p • (b p • B ⟨a, ⟨s a, h⟩⟩) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [smul_assoc]
    · simp only [h, dif_neg, not_false_eq_true, Finset.sum_const_zero]
  · intro A hAN p a i hi
    have hc : toE A ∘ₗ toE N = toE N ∘ₗ toE A := by
      refine LinearMap.ext fun y => ?_
      exact LinearMap.congr_fun hAN y
    rw [Basis.smulTower_repr]
    have := hA (toE A) hc a i hi
    rw [htoE] at this
    rw [this, map_zero, Finsupp.zero_apply]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
