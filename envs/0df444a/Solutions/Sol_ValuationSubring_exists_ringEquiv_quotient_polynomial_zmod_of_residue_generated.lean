-- Prove2me | solution 1 for ValuationSubring.exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7cd269d9-ba6b-54fe-8b13-d8efbe29507b

import Mathlib
import Theorems.Thm_AlgHom_range_eq_range_aeval_X_of_isIntegral_adjoin_singleton
import Theorems.Thm_IntermediateField_exists_algEquiv_adjoin_simple_ratFunc_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

universe u

open Polynomial

theorem solution
    {F : Type u} [Field F] (W : ValuationSubring F) (p : ℕ) [Fact p.Prime]
    (hp0 : ((p : ℕ) : F) ≠ 0) (hpW : ((p : ℕ) : F) ∈ W.nonunits)
    (A : Subalgebra ℤ F) (hAW : ∀ a : F, a ∈ A → a ∈ W)
    (s : F) (hs : s ∈ A) (hint : ∀ a : F, a ∈ A → IsIntegral ↥(Algebra.adjoin ℤ ({s} : Set F)) a)
    (hgen : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.aeval s P ∈ W ∧ (Polynomial.aeval s P)⁻¹ ∈ W)
    (t : F) (ht : t ∈ A)
    (hres : ∀ x : F, x ∈ W → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      x * Polynomial.aeval t Q - Polynomial.aeval t P ∈ W.nonunits)
    (P₀ : Polynomial ℤ) (hsP₀ : s - Polynomial.aeval t P₀ ∈ W.nonunits)
    (𝔭 : Ideal ↥A) (h𝔭 : ∀ a : ↥A, a ∈ 𝔭 ↔ (a : F) ∈ W.nonunits) :
    ∃ e : (↥A ⧸ 𝔭) ≃+* Polynomial (ZMod p),
      ∀ (a : ↥A) (P : Polynomial ℤ), ((a : F) - Polynomial.aeval t P) ∈ W.nonunits →
        e (Ideal.Quotient.mk 𝔭 a) = P.map (Int.castRingHom (ZMod p)) := by
  classical
  have hpprime : p.Prime := Fact.out

  let toW : ↥A →+* ↥W := A.val.toRingHom.codRestrict W.toSubring fun a => hAW a a.2
  have htoW : ∀ a : ↥A, ((toW a : ↥W) : F) = a := fun a => rfl
  let ψ : ↥A →+* IsLocalRing.ResidueField ↥W := (IsLocalRing.residue ↥W).comp toW
  have hψker : ∀ a : ↥A, ψ a = 0 ↔ a ∈ 𝔭 := by
    intro a
    rw [h𝔭, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hψsub : ∀ a b : ↥A, ((a : F) - (b : F)) ∈ W.nonunits → ψ a = ψ b := by
    intro a b hab
    rw [← sub_eq_zero, ← map_sub, hψker, h𝔭]
    simpa using hab

  have hpA : ((p : ℕ) : ↥A) ∈ 𝔭 := by rw [h𝔭]; simpa using hpW
  have hpκ : ((p : ℕ) : IsLocalRing.ResidueField ↥W) = 0 := by
    rw [← map_natCast ψ, hψker]; exact hpA
  haveI : CharP (IsLocalRing.ResidueField ↥W) p := (CharP.charP_iff_prime_eq_zero hpprime).mpr hpκ
  have h𝔭top : 𝔭 ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, h𝔭]
    intro h
    rw [ValuationSubring.mem_nonunits_iff] at h
    simp at h
  haveI : Nontrivial (↥A ⧸ 𝔭) :=
    ⟨⟨0, 1, fun h => h𝔭top (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  have hpB : ((p : ℕ) : ↥A ⧸ 𝔭) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔭), Ideal.Quotient.eq_zero_iff_mem]; exact hpA
  haveI : CharP (↥A ⧸ 𝔭) p := (CharP.charP_iff_prime_eq_zero hpprime).mpr hpB
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥W) := ZMod.algebra _ p
  letI : Algebra (ZMod p) (↥A ⧸ 𝔭) := ZMod.algebra _ p

  have hnu : ∀ x : F, x ≠ 0 → x ∈ W → x⁻¹ ∈ W → x ∉ W.nonunits := by
    intro x hx0 hx hinv h
    rw [ValuationSubring.mem_nonunits_iff] at h
    have h1 : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hinv
    have hpos : 0 < W.valuation x := zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hx0)
    rw [map_inv₀, inv_le_one₀ hpos] at h1
    exact (lt_irrefl _) (lt_of_lt_of_le h h1)
  have hnu_mul : ∀ x y : F, x ∈ W.nonunits → y ∈ W → x * y ∈ W.nonunits := by
    intro x y hx hy
    rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
    rw [map_mul]
    calc W.valuation x * W.valuation y ≤ W.valuation x * 1 := by
          gcongr; exact (W.valuation_le_one_iff _).mpr hy
      _ < 1 := by rwa [mul_one]
  have hnu_add : ∀ x y : F, x ∈ W.nonunits → y ∈ W.nonunits → x + y ∈ W.nonunits := by
    intro x y hx hy
    rw [ValuationSubring.mem_nonunits_iff] at hx hy ⊢
    exact lt_of_le_of_lt (W.valuation.map_add x y) (max_lt hx hy)
  have hnu_neg : ∀ x : F, x ∈ W.nonunits → -x ∈ W.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
    rwa [Valuation.map_neg]
  have hnu_mem : ∀ x : F, x ∈ W.nonunits → x ∈ W := fun x hx =>
    (W.valuation_le_one_iff _).mp (le_of_lt ((ValuationSubring.mem_nonunits_iff _).mp hx))

  set tA : ↥A := ⟨t, ht⟩ with htA
  have haevalA : ∀ P : Polynomial ℤ, ((aeval tA P : ↥A) : F) = aeval t P := fun P =>
    (Polynomial.aeval_algHom_apply A.val tA P).symm
  have hmapsurj : ∀ Pb : Polynomial (ZMod p), ∃ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) = Pb :=
    fun Pb => Polynomial.map_surjective _ (ZMod.intCast_surjective) Pb
  set sA : ↥A := ⟨s, hs⟩ with hsA
  have haevalsA : ∀ P : Polynomial ℤ, ((aeval sA P : ↥A) : F) = aeval s P := fun P =>
    (Polynomial.aeval_algHom_apply A.val sA P).symm

  have hunit : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 → aeval s P ∉ W.nonunits := by
    intro P hP hmem
    by_cases h0 : aeval s P = 0
    ·
      have hP' : (P + C (p : ℤ)).map (Int.castRingHom (ZMod p)) ≠ 0 := by
        rw [Polynomial.map_add, Polynomial.map_C]; simpa using hP
      have h1 := hgen (P + C (p : ℤ)) hP'
      have hval : aeval s (P + C (p : ℤ)) = ((p : ℕ) : F) := by
        rw [map_add, h0, zero_add, Polynomial.aeval_C]; simp
      rw [hval] at h1
      exact hnu _ hp0 h1.1 h1.2 hpW
    · exact hnu _ h0 (hgen P hP).1 (hgen P hP).2 hmem

  set tb : IsLocalRing.ResidueField ↥W := ψ tA with htb
  have hψaeval' : ∀ (y : ↥A) (P : Polynomial ℤ),
      ψ (aeval y P) = aeval (ψ y) (P.map (Int.castRingHom (ZMod p))) := by
    have hcomp : (algebraMap (ZMod p) (IsLocalRing.ResidueField ↥W)).comp (Int.castRingHom (ZMod p)) =
        algebraMap ℤ (IsLocalRing.ResidueField ↥W) := RingHom.ext_int _ _
    intro y P
    rw [Polynomial.aeval_def (R := ZMod p), Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact (Polynomial.aeval_algHom_apply ψ.toIntAlgHom y P).symm
  have hψaeval : ∀ P : Polynomial ℤ, ψ (aeval tA P) = aeval tb (P.map (Int.castRingHom (ZMod p))) :=
    fun P => hψaeval' tA P

  have hsb : Transcendental (ZMod p) (ψ sA) := by
    rintro ⟨Pb, hPb0, hPb⟩
    obtain ⟨P, rfl⟩ := hmapsurj Pb
    have hP : P.map (Int.castRingHom (ZMod p)) ≠ 0 := hPb0
    apply hunit P hP
    rw [← haevalsA, ← h𝔭, ← hψker, hψaeval']
    exact hPb

  have hst : ψ sA = aeval tb (P₀.map (Int.castRingHom (ZMod p))) := by
    rw [← hψaeval]
    exact hψsub sA (aeval tA P₀) (by simpa [haevalA] using hsP₀)
  have htb : Transcendental (ZMod p) tb := by
    intro halg
    apply hsb
    rw [hst]
    have hint' : IsIntegral (ZMod p) tb := isAlgebraic_iff_isIntegral.mp halg
    have hle : Algebra.adjoin (ZMod p) ({tb} : Set (IsLocalRing.ResidueField ↥W)) ≤
        integralClosure (ZMod p) (IsLocalRing.ResidueField ↥W) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hint')
    exact isAlgebraic_iff_isIntegral.mpr (hle (Polynomial.aeval_mem_adjoin_singleton _ _))
  have haevalb : ∀ Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 →
      aeval tb (Q.map (Int.castRingHom (ZMod p))) ≠ 0 := fun Q hQ h =>
    hQ (transcendental_iff_injective.mp htb (by rw [h, map_zero]))

  have hrange : ∀ a : ↥A, ψ a ∈ IntermediateField.adjoin (ZMod p) ({tb} : Set (IsLocalRing.ResidueField ↥W)) := by
    intro a
    obtain ⟨P, Q, hQ, hPQ⟩ := hres a (hAW a a.2)
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨P.map (Int.castRingHom (ZMod p)), Q.map (Int.castRingHom (ZMod p)), ?_⟩
    rw [eq_div_iff (haevalb Q hQ), ← hψaeval, ← hψaeval, ← map_mul, ← sub_eq_zero, ← map_sub, hψker, h𝔭]
    simpa [haevalA] using hPQ

  obtain ⟨e₁, he₁⟩ := IntermediateField.exists_algEquiv_adjoin_simple_ratFunc_of_transcendental (ZMod p)
    (IsLocalRing.ResidueField ↥W) tb htb

  let ψ₁ : ↥A →+* ↥(IntermediateField.adjoin (ZMod p) ({tb} : Set (IsLocalRing.ResidueField ↥W))) :=
    ψ.codRestrict _ hrange
  let φ₀ : ↥A →+* RatFunc (ZMod p) := e₁.toRingEquiv.toRingHom.comp ψ₁
  have hφ₀ : ∀ a : ↥A, φ₀ a = e₁ (ψ₁ a) := fun a => rfl
  have hφ₀ker : ∀ a : ↥A, φ₀ a = 0 ↔ a ∈ 𝔭 := by
    intro a
    rw [hφ₀, map_eq_zero_iff _ e₁.injective, ← hψker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let φ : ↥A ⧸ 𝔭 →+* RatFunc (ZMod p) :=
    Ideal.Quotient.lift 𝔭 φ₀ fun a ha => (hφ₀ker a).mpr ha
  have hφmk : ∀ a : ↥A, φ (Ideal.Quotient.mk 𝔭 a) = φ₀ a := fun a => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hφ₀ker a).mp hb

  let φa : (↥A ⧸ 𝔭) →ₐ[ZMod p] RatFunc (ZMod p) :=
    { toRingHom := φ
      commutes' := fun r => by
        obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
        simp }
  have hφt : φa (Ideal.Quotient.mk 𝔭 tA) = RatFunc.X := by
    change φ₀ tA = RatFunc.X
    rw [hφ₀, ← he₁]
    rfl

  have hmk_sub : ∀ a b : ↥A, ((a : F) - (b : F)) ∈ W.nonunits →
      Ideal.Quotient.mk 𝔭 a = Ideal.Quotient.mk 𝔭 b := by
    intro a b hab
    rw [Ideal.Quotient.eq, h𝔭]
    simpa using hab
  have haevalB : ∀ (y : ↥A) (Q : Polynomial ℤ),
      Ideal.Quotient.mk 𝔭 (aeval y Q) = aeval (Ideal.Quotient.mk 𝔭 y) Q := fun y Q =>
    (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ 𝔭) y Q).symm
  have hsB : Ideal.Quotient.mk 𝔭 sA ∈
      Algebra.adjoin (ZMod p) ({Ideal.Quotient.mk 𝔭 tA} : Set (↥A ⧸ 𝔭)) := by
    rw [hmk_sub sA (aeval tA P₀) (by simpa [haevalA] using hsP₀), haevalB tA]
    have : aeval (Ideal.Quotient.mk 𝔭 tA) P₀ =
        aeval (Ideal.Quotient.mk 𝔭 tA) (P₀.map (algebraMap ℤ (ZMod p))) := by
      rw [Polynomial.aeval_def (R := ZMod p), Polynomial.eval₂_map,
        show (algebraMap (ZMod p) (↥A ⧸ 𝔭)).comp (algebraMap ℤ (ZMod p)) = algebraMap ℤ (↥A ⧸ 𝔭) from
          RingHom.ext_int _ _, ← Polynomial.aeval_def]
    rw [this]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  have hintB : ∀ b : ↥A ⧸ 𝔭,
      IsIntegral ↥(Algebra.adjoin (ZMod p) ({Ideal.Quotient.mk 𝔭 tA} : Set (↥A ⧸ 𝔭))) b := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b

    have hBA : Algebra.adjoin ℤ ({s} : Set F) ≤ A := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
    letI : Algebra ↥(Algebra.adjoin ℤ ({s} : Set F)) ↥A := (Subalgebra.inclusion hBA).toAlgebra
    haveI : IsScalarTower ↥(Algebra.adjoin ℤ ({s} : Set F)) ↥A F := IsScalarTower.of_algebraMap_eq fun x => rfl
    have ha : IsIntegral ↥(Algebra.adjoin ℤ ({s} : Set F)) a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ ↥A F) Subtype.val_injective).mp (hint a a.2)

    have hle : ∀ x : ↥(Algebra.adjoin ℤ ({s} : Set F)),
        Ideal.Quotient.mk 𝔭 (algebraMap _ ↥A x) ∈
          Algebra.adjoin (ZMod p) ({Ideal.Quotient.mk 𝔭 tA} : Set (↥A ⧸ 𝔭)) := by
      intro x
      have hx : (x : F) ∈ (aeval s : Polynomial ℤ →ₐ[ℤ] F).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact x.2
      obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).mp hx
      have hxeq : algebraMap _ ↥A x = aeval sA Q :=
        Subtype.ext (hQ.symm.trans (Polynomial.aeval_algHom_apply A.val sA Q))
      rw [hxeq, haevalB sA]

      set S := Algebra.adjoin (ZMod p) ({Ideal.Quotient.mk 𝔭 tA} : Set (↥A ⧸ 𝔭)) with hSdef
      have hmem : (S.val.toRingHom.toIntAlgHom (aeval (⟨_, hsB⟩ : ↥S) Q)) ∈ S := (aeval _ Q : ↥S).2
      have heq : S.val.toRingHom.toIntAlgHom (aeval (⟨_, hsB⟩ : ↥S) Q) = aeval (Ideal.Quotient.mk 𝔭 sA) Q :=
        (Polynomial.aeval_algHom_apply S.val.toRingHom.toIntAlgHom ⟨_, hsB⟩ Q).symm
      exact heq ▸ hmem

    let φ₁' : ↥(Algebra.adjoin ℤ ({s} : Set F)) →+* ↥(Algebra.adjoin (ZMod p) ({Ideal.Quotient.mk 𝔭 tA} : Set (↥A ⧸ 𝔭))) :=
      ((Ideal.Quotient.mk 𝔭).comp (algebraMap _ ↥A)).codRestrict _ hle
    exact ha.map_of_comp_eq φ₁' (Ideal.Quotient.mk 𝔭) (by ext x; rfl)

  have hrangeφ := AlgHom.range_eq_range_aeval_X_of_isIntegral_adjoin_singleton (ZMod p) (↥A ⧸ 𝔭)
    (Ideal.Quotient.mk 𝔭 tA) hintB φa hφt
  have haevX : ∀ q : Polynomial (ZMod p),
      aeval (RatFunc.X : RatFunc (ZMod p)) q = algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) q := by
    intro q
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  have hinjX : Function.Injective
      (aeval (RatFunc.X : RatFunc (ZMod p)) : Polynomial (ZMod p) →ₐ[ZMod p] RatFunc (ZMod p)) := by
    intro a b h
    have h' : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) a =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) b := by rwa [haevX, haevX] at h
    exact IsFractionRing.injective (Polynomial (ZMod p)) (RatFunc (ZMod p)) h'
  have hφainj : Function.Injective φa := hφinj
  let eφ : (↥A ⧸ 𝔭) ≃ₐ[ZMod p] ↥φa.range := AlgEquiv.ofInjective φa hφainj
  let eX : Polynomial (ZMod p) ≃ₐ[ZMod p] ↥(aeval (RatFunc.X : RatFunc (ZMod p))).range :=
    AlgEquiv.ofInjective _ hinjX
  let eR : ↥φa.range ≃ₐ[ZMod p] ↥(aeval (RatFunc.X : RatFunc (ZMod p))).range :=
    Subalgebra.equivOfEq _ _ hrangeφ
  let e : (↥A ⧸ 𝔭) ≃ₐ[ZMod p] Polynomial (ZMod p) := (eφ.trans eR).trans eX.symm
  have he : ∀ b : ↥A ⧸ 𝔭, aeval (RatFunc.X : RatFunc (ZMod p)) (e b) = φa b := by
    intro b
    have h1 : eX (e b) = eR (eφ b) := by
      simp only [e, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    have h2 := congrArg Subtype.val h1
    exact h2
  refine ⟨e.toRingEquiv, ?_⟩
  intro a P haP
  have hmk : Ideal.Quotient.mk 𝔭 a = aeval (Ideal.Quotient.mk 𝔭 tA) P := by
    rw [hmk_sub a (aeval tA P) (by simpa [haevalA] using haP), haevalB]
  apply hinjX
  have hmapP : aeval (Ideal.Quotient.mk 𝔭 tA) P =
      aeval (Ideal.Quotient.mk 𝔭 tA) (P.map (Int.castRingHom (ZMod p))) := by
    rw [Polynomial.aeval_def (R := ZMod p), Polynomial.eval₂_map,
      show (algebraMap (ZMod p) (↥A ⧸ 𝔭)).comp (Int.castRingHom (ZMod p)) = algebraMap ℤ (↥A ⧸ 𝔭) from
        RingHom.ext_int _ _, ← Polynomial.aeval_def]
  change aeval (RatFunc.X : RatFunc (ZMod p)) (e (Ideal.Quotient.mk 𝔭 a)) = _
  rw [he, hmk, hmapP, ← Polynomial.aeval_algHom_apply φa, hφt]

end S_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated
end P2MW
export P2MW.S_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated (solution)
