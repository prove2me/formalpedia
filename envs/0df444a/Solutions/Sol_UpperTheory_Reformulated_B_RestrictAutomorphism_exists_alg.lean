-- Prove2me | solution 1 for UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:34:11.254246+00:00
-- url     : https://prove2.me/submissions/5d1d5fe3-9303-4550-bc08-55d5ab2b38ec

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormSubgroupOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RestrictAutomorphism
import Theorems.Thm_UpperTheory_Reformulated_B_WittVectorTrivializingMatrix_exists_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.RestrictAutomorphism
private theorem hom_unique {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (φ ψ : ℤ_[p] →+* WittVector p R) : φ = ψ := by
  ext1 x
  rw [← sub_eq_zero]
  ext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (i + 1) x)
  have hx : x = y * (p : ℤ_[p]) ^ (i + 1) + (x.appr (i + 1) : ℤ_[p]) := by
    rw [hy]; ring
  have h : φ x - ψ x = (φ y - ψ y) * (p : WittVector p R) ^ (i + 1) := by
    conv_lhs => rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self i), WittVector.zero_coeff]
end UpperTheory.Reformulated.B.RestrictAutomorphism
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.RestrictAutomorphism
theorem _root_.solution :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  (∀ (g : G),
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.RestrictAutomorphism.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map ((ρ : G → R ≃+* R) g).toRingHom) : WittVector p R → WittVector p R) =
                        W) ∧
                    ∀ (i j : Fin r) (n : ℕ), ∃ (m : ℕ), (0 : ℕ) < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n := by
  intro p hp G _ R _ ρ _ _ _ _ _ hopen r M hM hker
  haveI : CharP (algPart p R) p := inferInstance
  obtain ⟨V, hV, hVeq⟩ := UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg (p := p) (restrictHom p ρ)
    (fun y m hm hy => (hopen y m hm (by simpa using congrArg Subtype.val hy)).mono
      fun g hg => Subtype.ext hg)
    M hM
    (fun g hg => hker g fun m hm y hy =>
      congrArg Subtype.val (hg m hm ⟨y, m, hm, hy⟩ (Subtype.ext (by simpa using hy))))
  let ι : WittVector p (algPart p R) →+* WittVector p R := WittVector.map (algPart p R).subtype
  refine ⟨V.map ι, ?_, fun g => ?_, fun i j n => ?_⟩
  · have h := hV.map ι
    rwa [RingHom.map_det] at h
  · have h := congrArg (fun A => A.map ι) (hVeq g (restrictHom p ρ g).toRingHom fun _ _ _ _ => rfl)
    have h1 : (M g).map (zlW p R) =
        ((M g).map (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))).map ι := by
      rw [hom_unique (zlW p R) (ι.comp (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))),
        RingHom.coe_comp, Matrix.map_map]
    have h2 : (V.map ι).map (WittVector.map (ρ g).toRingHom) =
        (V.map (WittVector.map (restrictHom p ρ g).toRingHom)).map ι := by
      ext i j n
      simp only [Matrix.map_apply, ι, WittVector.map_coeff]
      rfl
    rw [h1, h2, ← Matrix.map_mul]
    exact h
  · simp only [Matrix.map_apply, ι, WittVector.map_coeff]
    exact ((V i j).coeff n).2
end UpperTheory.Reformulated.B.RestrictAutomorphism
