-- Prove2me | solution 1 for WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2422b524-0399-515c-b5d2-10ea5a9c89f1

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_HeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two

set_option autoImplicit false

noncomputable section

open CuspForm

namespace LevelRaising

section OldEmbedding

variable {N L : ℕ} (k : ℤ)

private theorem Gamma0_le_of_dvd (hNL : N ∣ L) :
    CongruenceSubgroup.Gamma0 L ≤ CongruenceSubgroup.Gamma0 N := fun A hA => by
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  have h := congrArg (ZMod.castHom hNL (ZMod N)) hA
  rwa [map_intCast, map_zero] at h

private theorem Gamma0GL_le_of_dvd (hNL : N ∣ L) :
    ((CongruenceSubgroup.Gamma0 L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le_of_dvd hNL)

private def oldEmb (hNL : N ∣ L) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 L) k where
  toFun f :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ =>
        SlashInvariantFormClass.slash_action_eq f γ (Gamma0GL_le_of_dvd hNL hγ)
      holo' := CuspFormClass.holo f
      zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f (hc.mono (Gamma0GL_le_of_dvd hNL)) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem coe_oldEmb (hNL : N ∣ L) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ⇑(oldEmb k hNL f) = ⇑f := rfl

private theorem oldEmb_injective (hNL : N ∣ L) : Function.Injective (oldEmb k hNL) := fun _ _ h =>
  DFunLike.ext' (congrArg (fun x : CuspForm (CongruenceSubgroup.Gamma0 L) k => (x : UpperHalfPlane → ℂ)) h)

private theorem heckeTLin_oldEmb (hNL : N ∣ L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    heckeTLin k hℓ hℓL (oldEmb k hNL f) = oldEmb k hNL (heckeTLin k hℓ hℓN f) :=
  DFunLike.coe_injective rfl

private theorem heckeTLin_comp_oldEmb (hNL : N ∣ L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N) :
    heckeTLin k hℓ hℓL ∘ₗ oldEmb k hNL = oldEmb k hNL ∘ₗ heckeTLin k hℓ hℓN :=
  LinearMap.ext fun f => heckeTLin_oldEmb k hNL hℓ hℓL hℓN f

end OldEmbedding

section Presentation

variable (N D : ℕ) [NeZero N] [NeZero D] (k : ℤ) (S : Set ℕ)

private def GoodIdx : Type := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N * D}

variable {N D S} in
omit [NeZero N] [NeZero D] in
private theorem GoodIdx.not_dvd (ℓ : GoodIdx N D S) : ¬ ℓ.1 ∣ N := fun h => ℓ.2.2.2 (h.mul_right D)

private def genBig (ℓ : GoodIdx N D S) : heckeAlgebra (N * D) k S := heckeAlgebra.T ℓ.2.1 ℓ.2.2.2 ℓ.2.2.1

private def genSmall (ℓ : GoodIdx N D S) : heckeAlgebra N k S := heckeAlgebra.T ℓ.2.1 ℓ.not_dvd ℓ.2.2.1

private def evBig : MvPolynomial (GoodIdx N D S) ℤ →ₐ[ℤ] heckeAlgebra (N * D) k S :=
  MvPolynomial.aeval (genBig N D k S)

private def evSmall : MvPolynomial (GoodIdx N D S) ℤ →ₐ[ℤ] heckeAlgebra N k S :=
  MvPolynomial.aeval (genSmall N D k S)

variable (hSN : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hSD : ∀ q : ℕ, q.Prime → q ∣ D → q ∈ S)
include hSN hSD

private theorem heckeGenerators_big_eq :
    heckeGenerators (N * D) k S = (heckeAlgebra (N * D) k S).val '' Set.range (genBig N D k S) := by
  ext T
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Subalgebra.coe_val]
  constructor
  · rintro (⟨ℓ, hℓ, hℓND, hℓS, rfl⟩ | ⟨q, hqND, hq, hqS, rfl⟩)
    · exact ⟨⟨ℓ, hℓ, hℓS, hℓND⟩, rfl⟩
    · rcases (Nat.Prime.dvd_mul hq).mp hqND with h | h
      · exact absurd (hSN q hq h) hqS
      · exact absurd (hSD q hq h) hqS
  · rintro ⟨⟨ℓ, hℓ, hℓS, hℓND⟩, rfl⟩
    exact Or.inl ⟨ℓ, hℓ, hℓND, hℓS, rfl⟩

omit [NeZero D] in
private theorem heckeGenerators_small_eq :
    heckeGenerators N k S = (heckeAlgebra N k S).val '' Set.range (genSmall N D k S) := by
  ext T
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Subalgebra.coe_val]
  constructor
  · rintro (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
    · have hℓND : ¬ ℓ ∣ N * D := fun h => by
        rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
        · exact hℓN h
        · exact hℓS (hSD ℓ hℓ h)
      exact ⟨⟨ℓ, hℓ, hℓS, hℓND⟩, rfl⟩
    · exact absurd (hSN q hq hqN) hqS
  · rintro ⟨⟨ℓ, hℓ, hℓS, hℓND⟩, rfl⟩
    exact Or.inl ⟨ℓ, hℓ, GoodIdx.not_dvd (⟨ℓ, hℓ, hℓS, hℓND⟩ : GoodIdx N D S), hℓS, rfl⟩

omit [NeZero N] hSN hSD in

private theorem adjoin_eq_top_of_image {A : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k))}
    {s : Set A} (h : Algebra.adjoin ℤ (A.val '' s) = A) : Algebra.adjoin ℤ s = ⊤ := by
  apply Subalgebra.map_injective (f := A.val) Subtype.val_injective
  rw [← Algebra.adjoin_image, h, Algebra.map_top, Subalgebra.range_val]

private theorem evBig_surjective : Function.Surjective (evBig N D k S) := by
  rw [← AlgHom.range_eq_top, evBig, MvPolynomial.aeval_range]
  haveI : NeZero (N * D) := inferInstance
  exact adjoin_eq_top_of_image (N * D) k (by rw [← heckeGenerators_big_eq N D k S hSN hSD]; rfl)

omit [NeZero D] in
private theorem evSmall_surjective : Function.Surjective (evSmall N D k S) := by
  rw [← AlgHom.range_eq_top, evSmall, MvPolynomial.aeval_range]
  exact adjoin_eq_top_of_image N k (by rw [← heckeGenerators_small_eq N D k S hSN hSD]; rfl)

omit hSN hSD in

private theorem evBig_comp_oldEmb (P : MvPolynomial (GoodIdx N D S) ℤ) :
    ((evBig N D k S P : heckeAlgebra (N * D) k S) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 (N * D)) k)) ∘ₗ oldEmb k (dvd_mul_right N D) =
      oldEmb k (dvd_mul_right N D) ∘ₗ
        ((evSmall N D k S P : heckeAlgebra N k S) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) := by
  induction P using MvPolynomial.induction_on with
  | C n =>
    ext f : 1
    simp only [evBig, evSmall, MvPolynomial.aeval_C, LinearMap.comp_apply]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply,
      Module.End.one_apply, Module.End.one_apply, map_zsmul]
  | add p q hp hq =>
    simp only [evBig, evSmall] at hp hq ⊢
    rw [map_add, map_add, Subalgebra.coe_add, Subalgebra.coe_add, LinearMap.add_comp,
      LinearMap.comp_add, hp, hq]
  | mul_X p ℓ hp =>
    simp only [evBig, evSmall] at hp ⊢
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Subalgebra.coe_mul,
      Subalgebra.coe_mul, genBig, genSmall, heckeAlgebra.coe_T, heckeAlgebra.coe_T,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc,
      heckeTLin_comp_oldEmb k (dvd_mul_right N D) ℓ.2.1 ℓ.2.2.2 ℓ.not_dvd, ← LinearMap.comp_assoc,
      hp, LinearMap.comp_assoc]

omit hSN hSD in

private theorem ker_evBig_le_ker_evSmall :
    RingHom.ker (evBig N D k S).toRingHom ≤ RingHom.ker (evSmall N D k S).toRingHom := by
  intro P hP
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hP ⊢
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply oldEmb_injective k (dvd_mul_right N D)
  have h := congrArg (fun T => T f) (evBig_comp_oldEmb N D k S P)
  simp only [LinearMap.comp_apply, hP, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h
  rw [ZeroMemClass.coe_zero, LinearMap.zero_apply, map_zero]
  exact h.symm

private def restrictHom : heckeAlgebra (N * D) k S →+* heckeAlgebra N k S :=
  (evBig N D k S).toRingHom.liftOfSurjective (evBig_surjective N D k S hSN hSD)
    ⟨(evSmall N D k S).toRingHom, ker_evBig_le_ker_evSmall N D k S⟩

private theorem restrictHom_evBig (P : MvPolynomial (GoodIdx N D S) ℤ) :
    restrictHom N D k S hSN hSD (evBig N D k S P) = evSmall N D k S P :=
  (evBig N D k S).toRingHom.liftOfRightInverse_comp_apply _ _ _ P

private theorem restrictHom_surjective : Function.Surjective (restrictHom N D k S hSN hSD) := fun y => by
  obtain ⟨P, rfl⟩ := evSmall_surjective N D k S hSN hSD y
  exact ⟨evBig N D k S P, restrictHom_evBig N D k S hSN hSD P⟩

private theorem restrictHom_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓND : ¬ ℓ ∣ N * D) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) :
    restrictHom N D k S hSN hSD (heckeAlgebra.T hℓ hℓND hℓS) = heckeAlgebra.T hℓ hℓN hℓS := by
  have h1 : (heckeAlgebra.T hℓ hℓND hℓS : heckeAlgebra (N * D) k S) =
      evBig N D k S (MvPolynomial.X ⟨ℓ, hℓ, hℓS, hℓND⟩) := by
    rw [evBig, MvPolynomial.aeval_X]; rfl
  have h2 : (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N k S) =
      evSmall N D k S (MvPolynomial.X ⟨ℓ, hℓ, hℓS, hℓND⟩) := by
    rw [evSmall, MvPolynomial.aeval_X]; rfl
  rw [h1, restrictHom_evBig, ← h2]

end Presentation

private theorem exists_ideal_heckeAlgebra_mul_of_ideal_heckeAlgebra (N D : ℕ) [NeZero N] [NeZero D]
    (k : ℤ) (S : Set ℕ)
    (hSN : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hSD : ∀ q : ℕ, q.Prime → q ∣ D → q ∈ S)
    (p : ℕ) (a : ℕ → ℤ) (Q : ℕ → Prop)
    (𝔪 : Ideal (heckeAlgebra N k S)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : heckeAlgebra N k S) ∈ 𝔪)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N k S) ∈ 𝔪) :
    ∃ 𝔪' : Ideal (heckeAlgebra (N * D) k S), 𝔪'.IsMaximal ∧
      (p : heckeAlgebra (N * D) k S) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓND : ¬ ℓ ∣ N * D), Q ℓ →
        heckeAlgebra.T hℓ hℓND hℓS - ((a ℓ : ℤ) : heckeAlgebra (N * D) k S) ∈ 𝔪' := by
  haveI := h𝔪
  let φ := restrictHom N D k S hSN hSD
  haveI : RingHomClass (heckeAlgebra (N * D) k S →+* heckeAlgebra N k S)
      (heckeAlgebra (N * D) k S) (heckeAlgebra N k S) := RingHom.instRingHomClass
  refine ⟨𝔪.comap φ, Ideal.comap_isMaximal_of_surjective φ (restrictHom_surjective N D k S hSN hSD),
    ?_, fun ℓ hℓ hℓS hℓND hQ => ?_⟩
  · rw [Ideal.mem_comap, map_natCast]
    exact hp𝔪
  · have hℓN : ¬ ℓ ∣ N := fun h => hℓND (h.mul_right D)
    rw [Ideal.mem_comap, RingHom.map_sub, map_intCast, restrictHom_T N D k S hSN hSD hℓ hℓND hℓS hℓN]
    exact hocc ℓ hℓ hℓS hℓN hQ

private theorem rc2_two_branch (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N']
    (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀)
    (𝔪ₖ : Ideal (heckeAlgebra N' 2 S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra (N' * p) 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N' * p),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exists_ideal_heckeAlgebra_mul_of_ideal_heckeAlgebra N' p 2 S₀ hS₀N
    (fun _ hq hqp => ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hqp) ▸ hS₀p)
    p (fun ℓ => W.apOfModel ℓ) W.IsGoodPrimeFor 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc

end LevelRaising
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two.LevelRaising"

theorem solution (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N']
    (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀)
    (𝔪ₖ : Ideal (heckeAlgebra N' 2 S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra (N' * p) 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N' * p),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ :=
  LevelRaising.rc2_two_branch p W N' S₀ hS₀p hS₀N 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc

end
end S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two (solution)
