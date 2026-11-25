-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.omega_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:20.915815+00:00
-- url     : https://prove2.me/submissions/e6999615-4fdc-426f-af96-43b449c22631

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_mem_augIdeal
import Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_sqIdeal_le
import Theorems.Thm_ReciprocityTheory_PGsh_Up_PullbackHopfOrder_mq_mk

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X N : Type} [AddCommGroup X] [AddCommGroup N]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution (q : ℕ) {g d : ℕ} (ψ : X →+ N) (χ : N →+ X) (hχψ : ∀ x, χ (ψ x) = x)
    (A : Submodule R (N → C)) (hA : ∀ f ∈ A, (fun n => f (ψ (χ n))) ∈ A)
    (φ : augIdeal A →ₗ[R] LieDualModP q R g) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = (sqIdeal (augIdeal A)).comap (augIdeal A).subtype)
    (F : Matrix (Fin g) (Fin g) R) (P1 : Matrix (Fin g) (Fin d) R) (P2 : Matrix (Fin d) (Fin g) R)
    (hF : P1 * P2 = F) (h21 : P2 * P1 = 1)
    (hlin : ∀ (f f' : augIdeal A) (l : Fin g → R),
      (∀ n, (f' : N → C) n = (f : N → C) (ψ (χ n))) →
      φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk (F *ᵥ l)) :
    Nonempty (OmAA (A.map (LinearMap.funLeft R C ψ)) ≃ₗ[R] LieDualModP q R d) := by
  classical
  have hM : P2 * F * P1 = 1 := by
    rw [← hF, ← Matrix.mul_assoc P2 P1 P2, h21, Matrix.one_mul, h21]
  have hψI : ∀ f ∈ augIdeal A,
      LinearMap.funLeft R C ψ f ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)) := by
    intro f hf
    rw [mem_augIdeal] at hf ⊢
    refine ⟨Submodule.mem_map_of_mem hf.1, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact hf.2
  have hχI : ∀ g ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)),
      LinearMap.funLeft R C χ g ∈ augIdeal A := by
    intro g hg
    rw [mem_augIdeal] at hg ⊢
    obtain ⟨⟨f, hf, rfl⟩, h0⟩ := hg
    refine ⟨hA f hf, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact h0
  let Φ0 : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] augIdeal A :=
    ((LinearMap.funLeft R C χ).comp (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype).codRestrict
      (augIdeal A) (fun g => hχI g.1 g.2)
  let Φ : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] LieDualModP q R d :=
    mq q P2 ∘ₗ φ ∘ₗ Φ0
  have hΦ : ∀ g, Φ g = mq q P2 (φ (Φ0 g)) := fun _ => rfl
  have hsurjΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, hf⟩ := hsurj (Submodule.Quotient.mk (P1 *ᵥ w))
    refine ⟨⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩, ?_⟩
    have h1 := hlin f (Φ0 ⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩) (P1 *ᵥ w) (fun n => rfl) hf
    rw [hΦ, h1, mq_mk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have hkerΦ : LinearMap.ker Φ = (sqIdeal (augIdeal (A.map (LinearMap.funLeft R C ψ)))).comap
      (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (φ (Φ0 u))
      have hfix := hlin (Φ0 u) (Φ0 u) l (fun n => by
        show (u : X → C) (χ n) = (u : X → C) (χ (ψ (χ n)))
        rw [hχψ]) hl.symm
      rw [← hl, mq_mk] at h0
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [hfix, ← hF, ← Matrix.mulVec_mulVec,
          show (Submodule.Quotient.mk (P1 *ᵥ (P2 *ᵥ l)) : LieDualModP q R g) =
            mq q P1 (Submodule.Quotient.mk (P2 *ᵥ l)) from rfl, h0, map_zero]
      have hmem : ((Φ0 u : augIdeal A) : N → C) ∈ sqIdeal (augIdeal A) := by
        have := LinearMap.mem_ker.2 hφ0
        rw [hker, Submodule.mem_comap] at this
        exact this
      have := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) hψI hmem)
      convert this using 1
      funext x
      show (u : X → C) x = (u : X → C) (χ (ψ x))
      rw [hχψ]
    · intro hu
      have h1 := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C χ) (fun _ _ => rfl) hχI hu)
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [← LinearMap.mem_ker, hker, Submodule.mem_comap]
        exact h1
      rw [hφ0, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerΦ.symm).trans (Φ.quotKerEquivOfSurjective hsurjΦ)⟩
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
