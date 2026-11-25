-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:09.390316+00:00
-- url     : https://prove2.me/submissions/84afaafe-3a2d-422d-8ee4-f35e422fb594

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_FiniteHZeroOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w v₁ v₂ v₃
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution [IsNoetherianRing R]
    (ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J) (ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J)
    (ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (ι : ∀ I, A I →ₗ[R] B I) (q : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hq : ∀ I J h m, q J (ρB I J h m) = ρC I J h (q I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (q I))
    (hex : ∀ I b, q I b = 0 ↔ ∃ a, ι I a = b)
    (hB : Module.Finite R (H B ρB 0)) (hA : Module.Finite R (H A ρA 1)) :
    Module.Finite R (H C ρC 0) := by
  have := hA
  have hιd := mapC_d (R := R) (G := A) (G' := B) ι hι
  have hqd := mapC_d (R := R) (G := B) (G' := C) q hq
  have hιinj : ∀ i, Function.Injective (mapC (R := R) (G := A) (G' := B) ι i) := fun i a b hab =>
    _root_.funext fun I => hinj I.1 (congrFun hab I)
  have hq0 : ∀ i (c : Cochain B i), mapC (R := R) (G := B) (G' := C) q i c = 0 ↔
      ∃ a, mapC (R := R) (G := A) (G' := B) ι i a = c := fun i c => by
    constructor
    · intro h
      choose a ha using fun I => (hex I.1 (c I)).mp (congrFun h I)
      exact ⟨a, _root_.funext ha⟩
    · rintro ⟨a, rfl⟩
      exact _root_.funext fun I => (hex I.1 _).mpr ⟨a I, rfl⟩

  obtain ⟨P, hP⟩ : ∃ P : Submodule R (Cochain B 0), ∀ w, w ∈ P ↔
      mapC (R := R) (G := B) (G' := C) q 1 (d B ρB 0 w) = 0 :=
    ⟨LinearMap.ker ((mapC (R := R) (G := B) (G' := C) q 1).comp (d B ρB 0)), fun _ => LinearMap.mem_ker⟩

  obtain ⟨θ, hθ0, hθs⟩ : ∃ θ : P →ₗ[R] H C ρC 0,
      (∀ p, θ p = 0 ↔ mapC (R := R) (G := B) (G' := C) q 0 p.1 = 0) ∧ Function.Surjective θ := by
    have hk : ∀ p : P, mapC (R := R) (G := B) (G' := C) q 0 p.1 ∈ LinearMap.ker (d C ρC 0) := fun p => by
      rw [LinearMap.mem_ker, ← hqd 0]; exact (hP p.1).mp p.2
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _
      ((mapC (R := R) (G := B) (G' := C) q 0).comp P.subtype) hk), fun p => ?_, fun h => ?_⟩
    · change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact Submodule.mem_bot R
    · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      choose w hw using fun I : Idx U 0 => hsurj I.1 (c.1 I)
      have hmw : mapC (R := R) (G := B) (G' := C) q 0 w = c.1 := _root_.funext hw
      refine ⟨⟨w, (hP w).mpr (by rw [hqd 0, hmw]; exact c.2)⟩, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk c
      congr 1
      exact Subtype.ext hmw

  have hdP : ∀ p : P, d B ρB 0 p.1 ∈ LinearMap.range (mapC (R := R) (G := A) (G' := B) ι 1) := fun p =>
    LinearMap.mem_range.mpr ((hq0 1 _).mp ((hP p.1).mp p.2))
  obtain ⟨g, hg⟩ : ∃ g : P →ₗ[R] Cochain A 1,
      ∀ p, mapC (R := R) (G := A) (G' := B) ι 1 (g p) = d B ρB 0 p.1 :=
    ⟨(LinearEquiv.ofInjective _ (hιinj 1)).symm.toLinearMap.comp
        (LinearMap.codRestrict _ ((d B ρB 0).comp P.subtype) hdP),
      fun p => congrArg Subtype.val ((LinearEquiv.ofInjective _ (hιinj 1)).apply_symm_apply _)⟩
  have hgk : ∀ p : P, g p ∈ LinearMap.ker (d A ρA 1) := fun p =>
    LinearMap.mem_ker.mpr (hιinj (1 + 1) ((hιd 1 (g p)).trans (by
      rw [hg, d_one_d_zero hρB, map_zero])))
  obtain ⟨ψ, hψ0⟩ : ∃ ψ : P →ₗ[R] H A ρA 1, ∀ p, ψ p = 0 ↔ ∃ g', d A ρA 0 g' = g p :=
    ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ g hgk), fun p => by
      change Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact LinearMap.mem_range⟩
  have hle : LinearMap.ker θ ≤ LinearMap.ker ψ := fun p hp => by
    obtain ⟨a, ha⟩ := (hq0 0 _).mp ((hθ0 p).mp hp)
    refine (hψ0 p).mpr ⟨a, hιinj 1 ?_⟩
    rw [hg, hιd 0, ha]

  let f := (LinearMap.ker θ).liftQ ψ hle
  have hZP : LinearMap.ker (d B ρB 0) ≤ P := fun z hz =>
    (hP z).mpr (by rw [LinearMap.mem_ker.mp hz, map_zero])
  let j := (LinearMap.ker θ).mkQ.comp (Submodule.inclusion hZP)
  have hker : LinearMap.ker f = LinearMap.range j := by
    apply le_antisymm
    · intro m hm
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hm' : ψ p = 0 := hm
      obtain ⟨g', hg'⟩ := (hψ0 p).mp hm'
      have hz : p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' ∈ LinearMap.ker (d B ρB 0) := by
        rw [LinearMap.mem_ker, map_sub, ← hιd 0, hg', hg, sub_self]
      have hqι : mapC (R := R) (G := B) (G' := C) q 0 (mapC (R := R) (G := A) (G' := B) ι 0 g') = 0 :=
        (hq0 0 _).mpr ⟨g', rfl⟩
      refine ⟨⟨_, hz⟩, (Submodule.Quotient.eq _).mpr ((hθ0 _).mpr ?_)⟩
      change mapC (R := R) (G := B) (G' := C) q 0
        (p.1 - mapC (R := R) (G := A) (G' := B) ι 0 g' - p.1) = 0
      rw [sub_sub_cancel_left, map_neg, hqι, neg_zero]
    · rintro _ ⟨z, rfl⟩
      show ψ (Submodule.inclusion hZP z) = 0
      refine (hψ0 _).mpr ⟨0, hιinj 1 ?_⟩
      rw [map_zero, map_zero, hg]
      exact (LinearMap.mem_ker.mp z.2).symm

  have hZfin : Module.Finite R (LinearMap.ker (d B ρB 0)) := by
    have : Module.Finite R (LinearMap.ker (d B ρB 0) ⧸
        (bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) := hB
    exact Module.Finite.equiv (Submodule.quotEquivOfEqBot
      ((bdry B ρB 0).comap (LinearMap.ker (d B ρB 0)).subtype) (eq_bot_iff.mpr fun z hz =>
      (Submodule.mem_bot R).mpr (Subtype.ext ((Submodule.mem_bot R).mp
        (show (z : Cochain B 0) ∈ (⊥ : Submodule R (Cochain B 0)) from hz)))))
  have hM : Module.Finite R (P ⧸ LinearMap.ker θ) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map j
  exact Module.Finite.equiv (θ.quotKerEquivOfSurjective hθs)
end GroundTheory.Heights₂.Heights.Kleiman.Cech
