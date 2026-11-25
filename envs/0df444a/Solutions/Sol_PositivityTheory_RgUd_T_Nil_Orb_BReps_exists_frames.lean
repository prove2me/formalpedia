-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:55:29.369053+00:00
-- url     : https://prove2.me/submissions/332fb576-6e4a-4c03-9ff1-d03b331b6595

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_DexGlobal
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_Imports
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_dex_global


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hr : IsReduced Z) :
    ∃ (M : Type) (_ : Fintype M) (L : M → Type) (_ : ∀ m, Fintype (L m)) (_ : ∀ m, Nonempty (L m))
      (R : Z → (m : M) → L m → L m → k) (o : (m : M) → L m → k),
      ∀ N : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * N = N * z) → IsNilpotent N → ∀ v : Fin n → k,
        Nonempty (Frame Z M L R o N v) := by
  letI iCR : CommRing Z :=
    { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  letI iM : Module Z (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toRingHom.comp
      Z.val.toRingHom)
  have hsmul : ∀ (z : Z) (u : Fin n → k), z • u = (z : Matrix (Fin n) (Fin n) k) *ᵥ u := fun z u => rfl
  haveI iST : IsScalarTower k Z (Fin n → k) := ⟨fun c z u => by
    rw [hsmul, hsmul, Subalgebra.coe_smul]
    ext i
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]⟩
  obtain ⟨M, fM, L, fL, hne, Rc, o, H⟩ :=
    @dex_global k _ Z iCR (Subalgebra.algebra Z) inferInstance hr (Fin n → k) _ iM _ iST inferInstance
  refine ⟨M, fM, L, fL, hne, Rc, o, ?_⟩
  intro N hNZ hNnil v
  let toZ : (A : Matrix (Fin n) (Fin n) k) → (∀ z ∈ Z, z * A = A * z) → ((Fin n → k) →ₗ[Z] (Fin n → k)) :=
    fun A hA =>
      { toFun := fun u => A *ᵥ u
        map_add' := fun u w => mulVec_add A u w
        map_smul' := fun z u => by
          show A *ᵥ ((z : Matrix (Fin n) (Fin n) k) *ᵥ u) = (z : Matrix (Fin n) (Fin n) k) *ᵥ (A *ᵥ u)
          rw [mulVec_mulVec, mulVec_mulVec, hA z z.2] }
  have hpow : ∀ j : ℕ, ∀ u, ((toZ N hNZ) ^ j) u = (N ^ j) *ᵥ u := by
    intro j
    induction j with
    | zero => intro u; simp
    | succ j ih =>
      intro u
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← mulVec_mulVec]
      rfl
  have hnil : IsNilpotent (toZ N hNZ) := by
    obtain ⟨K, hK⟩ := hNnil
    exact ⟨K, LinearMap.ext fun u => by rw [hpow, hK, zero_mulVec]; rfl⟩
  obtain ⟨ι, fι, l, s, β, h1, h2, h3, h4, h5, h6⟩ := H (toZ N hNZ) hnil v
  have hA : ∀ (A : Matrix (Fin n) (Fin n) k), (∀ z ∈ Z, z * A = A * z) → A * N = N * A →
      ∀ (m : M) (p : L m) (a : ι m) (i : Fin (l m a)), (i : ℕ) < s m a →
        (β.repr (A *ᵥ v)) ⟨m, (p, ⟨a, i⟩)⟩ = 0 := by
    intro A hAZ hAN m p a i hi
    refine h6 (toZ A hAZ) (LinearMap.ext fun u => ?_) m p a i hi
    show A *ᵥ (N *ᵥ u) = N *ᵥ (A *ᵥ u)
    rw [mulVec_mulVec, mulVec_mulVec, hAN]
  exact ⟨@Frame.mk k _ n Z M fM L fL Rc o N v ι fι l s β h1 h2 (fun z m p j => h3 z m p j) h4 h5 hA⟩
end PositivityTheory.RgUd.T.Nil.Orb.BReps
