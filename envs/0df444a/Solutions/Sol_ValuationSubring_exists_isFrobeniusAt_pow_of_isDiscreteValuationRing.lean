-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a8421da6-eb07-568c-953d-bbbaaf93b85d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
import Theorems.Thm_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing

set_option autoImplicit false

open scoped Pointwise
open IsLocalRing

namespace P2mKcFrobDvr

section ResAlg

variable {E : Type*} {M : Type*} [Field E] [Field M] [Algebra E M]

def inclHom (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O) : O →+* W where
  toFun x := ⟨algebraMap E M x, (h x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_inclHom (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O) (x : O) :
    ((inclHom O W h x : W) : M) = algebraMap E M x := rfl

scoped instance isLocalHom_inclHom (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O) : IsLocalHom (inclHom O W h) := by
  constructor
  intro x hx
  have hx0 : (x : E) ≠ 0 := by
    rintro h0
    apply hx.ne_zero
    exact Subtype.ext (by simp [h0])
  have hinv : (algebraMap E M x)⁻¹ ∈ W := by
    have h1 : W.valuation (algebraMap E M x) = 1 := (W.valuation_eq_one_iff _).mp hx
    rw [← W.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hxinvO : (x : E)⁻¹ ∈ O := by
    rw [← h, map_inv₀]
    exact hinv
  exact isUnit_iff_exists_inv.mpr ⟨⟨(x : E)⁻¹, hxinvO⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

@[reducible] noncomputable def resAlg (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O) :
    Algebra (ResidueField O) (ResidueField W) :=
  (ResidueField.map (inclHom O W h)).toAlgebra

theorem resAlg_algebraMap_residue (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O) (a : O) :
    letI := resAlg O W h
    algebraMap (ResidueField O) (ResidueField W) (residue O a) =
      residue W ⟨algebraMap E M a, (h a).mpr a.2⟩ := rfl

theorem residueField_map_surjective (O : ValuationSubring E) (W : ValuationSubring M)
    (h : ∀ x : E, algebraMap E M x ∈ W ↔ x ∈ O)
    (hsurj : ∀ w : W, ∃ a : O, w - inclHom O W h a ∈ maximalIdeal W) :
    Function.Surjective (ResidueField.map (inclHom O W h)) := by
  intro y
  obtain ⟨w, rfl⟩ := residue_surjective y
  obtain ⟨a, ha⟩ := hsurj w
  refine ⟨residue O a, ?_⟩
  rw [ResidueField.map_residue]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have := Submodule.neg_mem _ ha
  rwa [neg_sub] at this

end ResAlg

section Basic

variable {K N : Type*} [Field K] [Field N] [Algebra K N]

theorem mem_nonunits_iff_eq_zero_or_inv_notMem (W : ValuationSubring N) (x : N) :
    x ∈ W.nonunits ↔ x = 0 ∨ x⁻¹ ∉ W := by
  by_cases hx : x = 0
  · subst hx
    simp only [true_or, iff_true]
    rw [ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one
  · rw [ValuationSubring.mem_nonunits_iff, ← W.valuation_le_one_iff, map_inv₀]
    have h0 : 0 < W.valuation x := (Valuation.pos_iff _).mpr hx
    rw [inv_le_one₀ h0, not_le]
    simp [hx]

theorem coe_smul_mem (W : ValuationSubring N) (σ : W.decompositionSubgroup K) (w : W) :
    ((σ • w : W) : N) = (σ : N ≃ₐ[K] N) w := rfl

theorem smul_residue (W : ValuationSubring N) (σ : W.decompositionSubgroup K) (w : W) :
    σ • residue W w = residue W (σ • w) := rfl

theorem smul_residue_eq_pow_iff (W : ValuationSubring N) (σ : W.decompositionSubgroup K) (w : W)
    (q : ℕ) :
    σ • residue W w = residue W w ^ q ↔ (σ : N ≃ₐ[K] N) w - (w : N) ^ q ∈ W.nonunits := by
  rw [smul_residue, ← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem mem_smul_iff (W : ValuationSubring N) (σ : N ≃ₐ[K] N) (x : N) :
    x ∈ σ • W ↔ σ.symm x ∈ W :=
  ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem smul_eq_of_forall_mem_iff (W : ValuationSubring N) (σ : N ≃ₐ[K] N)
    (h : ∀ x : N, x ∈ W ↔ σ x ∈ W) : σ • W = W := by
  ext x
  rw [mem_smul_iff, h (σ.symm x), AlgEquiv.apply_symm_apply]

end Basic

section FrobAut

theorem exists_algEquiv_apply_eq_pow_natCard (k κ : Type*) [Field k] [Finite k] [Field κ]
    [Algebra k κ] [Algebra.IsAlgebraic k κ] :
    ∃ τ : κ ≃ₐ[k] κ, ∀ x : κ, τ x = x ^ Nat.card k := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' k
  haveI := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP κ p := charP_of_injective_algebraMap (algebraMap k κ).injective p
  haveI : PerfectField κ := Algebra.IsAlgebraic.perfectField (K := k)
  have hq : Nat.card k = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  let e : κ ≃+* κ := iterateFrobeniusEquiv κ p n
  have he : ∀ x : κ, e x = x ^ Nat.card k := fun x => by
    rw [hq]; exact iterateFrobeniusEquiv_def κ p n x
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun a => ?_), fun x => he x⟩
  rw [he, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end FrobAut

section Infinite

variable {E L : Type*} [Field E] [Field L] [Algebra E L]
variable (O : ValuationSubring E) (W : ValuationSubring L)

def good (q : ℕ) (M : IntermediateField E L) : Set (L ≃ₐ[E] L) :=
  {σ | ∀ x : L, x ∈ M → (x ∈ W ↔ σ x ∈ W) ∧ (x ∈ W → σ x - x ^ q ∈ W.nonunits)}

variable {W}

theorem good_antitone (q : ℕ) {M M' : IntermediateField E L} (hMM' : M ≤ M') :
    good W q M' ⊆ good W q M := fun _ hσ x hx => hσ x (hMM' hx)

theorem mul_mem_good_iff (q : ℕ) (M : IntermediateField E L) (σ τ : L ≃ₐ[E] L)
    (hτ : τ ∈ M.fixingSubgroup) : σ * τ ∈ good W q M ↔ σ ∈ good W q M := by
  have hτx : ∀ x : L, x ∈ M → τ x = x := fun x hx => hτ ⟨x, hx⟩
  constructor
  · intro h x hx
    have := h x hx
    rwa [AlgEquiv.mul_apply, hτx x hx] at this
  · intro h x hx
    rw [AlgEquiv.mul_apply, hτx x hx]
    exact h x hx

theorem isOpen_of_mul_mem_iff (M : IntermediateField E L) [FiniteDimensional E M]
    (S : Set (L ≃ₐ[E] L))
    (hS : ∀ σ τ : L ≃ₐ[E] L, τ ∈ M.fixingSubgroup → (σ * τ ∈ S ↔ σ ∈ S)) : IsOpen S := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (M.fixingSubgroup : Set (L ≃ₐ[E] L)), ?_,
    (IntermediateField.fixingSubgroup_isOpen M).leftCoset σ, ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact (hS σ τ hτ).mpr hσ
  · exact ⟨1, M.fixingSubgroup.one_mem, mul_one σ⟩

theorem isClosed_good (q : ℕ) (M : IntermediateField E L) [FiniteDimensional E M] :
    IsClosed (good W q M) := by
  rw [← isOpen_compl_iff]
  refine isOpen_of_mul_mem_iff M _ fun σ τ hτ => ?_
  simp only [Set.mem_compl_iff]
  exact not_congr (mul_mem_good_iff q M σ τ hτ)

variable (W)

theorem good_nonempty [Normal E L] [Finite (ResidueField O)]
    (hW : ∀ x : E, algebraMap E L x ∈ W ↔ x ∈ O)
    (M : IntermediateField E L) [FiniteDimensional E M] [IsGalois E M] :
    (good W (Nat.card (ResidueField O)) M).Nonempty := by
  classical
  set WM : ValuationSubring M := W.comap (algebraMap M L) with hWMdef
  have hWM : ∀ x : E, algebraMap E M x ∈ WM ↔ x ∈ O := fun x => by
    rw [hWMdef, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hW x
  letI := resAlg O WM hWM
  obtain ⟨-, hnormal, hlift⟩ :=
    ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
      (E := E) (F := M) O WM hWM (fun a => resAlg_algebraMap_residue O WM hWM a)
  haveI := hnormal
  obtain ⟨τ, hτ⟩ := exists_algEquiv_apply_eq_pow_natCard (ResidueField O) (ResidueField WM)
  obtain ⟨σM, hσM⟩ := hlift τ
  set g : M ≃ₐ[E] M := (σM : M ≃ₐ[E] M) with hgdef
  have hgWM : g • WM = WM := σM.2
  refine ⟨g.liftNormal L, fun x hx => ?_⟩
  have hxL : x = algebraMap M L ⟨x, hx⟩ := rfl
  have hσx : g.liftNormal L x = algebraMap M L (g ⟨x, hx⟩) := by
    conv_lhs => rw [hxL]
    exact g.liftNormal_commutes L ⟨x, hx⟩
  constructor
  · rw [hσx]
    have h1 : x ∈ W ↔ (⟨x, hx⟩ : M) ∈ WM := by
      rw [hWMdef, ValuationSubring.mem_comap]; exact Iff.rfl
    have h2 : algebraMap M L (g ⟨x, hx⟩) ∈ W ↔ g ⟨x, hx⟩ ∈ WM := by
      rw [hWMdef, ValuationSubring.mem_comap]
    rw [h1, h2]
    conv_rhs => rw [← hgWM]
    exact ValuationSubring.smul_mem_pointwise_smul_iff.symm
  · intro hxW
    have hxWM : (⟨x, hx⟩ : M) ∈ WM := hxW
    have key := (smul_residue_eq_pow_iff WM σM ⟨⟨x, hx⟩, hxWM⟩ (Nat.card (ResidueField O))).mp
      (by rw [hσM, hτ])

    rw [mem_nonunits_iff_eq_zero_or_inv_notMem] at key ⊢
    rw [hσx]
    change (algebraMap M L (g ⟨x, hx⟩ - ⟨x, hx⟩ ^ Nat.card (ResidueField O)) = 0) ∨
      (algebraMap M L (g ⟨x, hx⟩ - ⟨x, hx⟩ ^ Nat.card (ResidueField O)))⁻¹ ∉ W
    rcases key with h0 | hinv
    · left
      have : (σM : M ≃ₐ[E] M) ⟨x, hx⟩ - (⟨x, hx⟩ : M) ^ Nat.card (ResidueField O) = 0 := h0
      rw [← hgdef] at this
      rw [this, map_zero]
    · right
      rw [← map_inv₀]
      exact hinv

theorem exists_mem_decompositionSubgroup_forall_smul_eq_pow [IsGalois E L]
    [Finite (ResidueField O)] (hW : ∀ x : E, algebraMap E L x ∈ W ↔ x ∈ O) :
    ∃ (σ : L ≃ₐ[E] L) (hσ : σ ∈ W.decompositionSubgroup E),
      ∀ x : ResidueField W,
        (⟨σ, hσ⟩ : W.decompositionSubgroup E) • x = x ^ Nat.card (ResidueField O) := by
  classical
  set q := Nat.card (ResidueField O) with hqdef

  have hne : (⋂ M : FiniteGaloisIntermediateField E L, good W q M.toIntermediateField).Nonempty := by
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    · intro M₁ M₂
      exact ⟨M₁ ⊔ M₂, good_antitone q (le_sup_left : M₁ ≤ M₁ ⊔ M₂),
        good_antitone q (le_sup_right : M₂ ≤ M₁ ⊔ M₂)⟩
    · intro M
      exact good_nonempty O W hW M.toIntermediateField
    · intro M
      exact (isClosed_good q M.toIntermediateField).isCompact
    · intro M
      exact isClosed_good q M.toIntermediateField
  obtain ⟨σ, hσ⟩ := hne
  rw [Set.mem_iInter] at hσ
  have hall : ∀ x : L, (x ∈ W ↔ σ x ∈ W) ∧ (x ∈ W → σ x - x ^ q ∈ W.nonunits) := by
    intro x
    exact hσ (FiniteGaloisIntermediateField.adjoin E {x}) x
      (FiniteGaloisIntermediateField.subset_adjoin E {x} (Set.mem_singleton x))
  have hσW : σ • W = W := smul_eq_of_forall_mem_iff W σ fun x => (hall x).1
  refine ⟨σ, hσW, fun x => ?_⟩
  obtain ⟨w, rfl⟩ := residue_surjective x
  rw [smul_residue_eq_pow_iff]
  exact (hall w).2 w.2

end Infinite

section Perfect

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

theorem mem_nonunits_comap_iff {F' : Type*} [Field F'] (A : ValuationSubring Ω) (f : F' →+* Ω)
    (x : F') : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_notMem, mem_nonunits_iff_eq_zero_or_inv_notMem,
    map_eq_zero_iff f f.injective, ValuationSubring.mem_comap, map_inv₀]

theorem exists_pow_sub_mem_maximalIdeal (O : ValuationSubring F) [Finite (ResidueField O)]
    (p : ℕ) [ExpChar F p] (n : ℕ) (z : O) :
    ∃ s : O, s ^ p ^ n - z ∈ maximalIdeal O := by
  haveI : ExpChar O p := RingHom.expChar (O.subtype) Subtype.coe_injective p

  let f : ResidueField O → ResidueField O := fun t => t ^ p ^ n
  have hf : Function.Injective f := by
    intro t t' htt'
    obtain ⟨s, rfl⟩ := residue_surjective t
    obtain ⟨s', rfl⟩ := residue_surjective t'
    change residue O s ^ p ^ n = residue O s' ^ p ^ n at htt'
    rw [← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, ← sub_pow_expChar_pow,
      IsLocalRing.residue_eq_zero_iff] at htt'
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ htt'
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hf) (residue O z)
  obtain ⟨s, rfl⟩ := residue_surjective t
  refine ⟨s, ?_⟩
  change residue O s ^ p ^ n = residue O z at ht
  rwa [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at ht

variable (A : ValuationSubring Ω)

abbrev traceOn (F : Type*) [Field F] [Algebra F Ω] (A : ValuationSubring Ω) : ValuationSubring F :=
  A.comap (algebraMap F Ω)

theorem lies_over_perfectClosure (x : F) :
    algebraMap F (perfectClosure F Ω) x ∈ traceOn (perfectClosure F Ω) A ↔ x ∈ traceOn F A := by
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]

theorem exists_sub_inclHom_mem_maximalIdeal_perfectClosure [Finite (ResidueField (traceOn F A))]
    (w : traceOn (perfectClosure F Ω) A) :
    ∃ a : traceOn F A,
      w - inclHom (traceOn F A) (traceOn (perfectClosure F Ω) A) (lies_over_perfectClosure A) a ∈
        maximalIdeal (traceOn (perfectClosure F Ω) A) := by
  set p := ringExpChar F with hpdef
  haveI : ExpChar Ω p := expChar_of_injective_ringHom (algebraMap F Ω).injective p
  haveI : ExpChar (perfectClosure F Ω) p :=
    RingHom.expChar (algebraMap (perfectClosure F Ω) Ω)
      (algebraMap (perfectClosure F Ω) Ω).injective p
  haveI : ExpChar (traceOn (perfectClosure F Ω) A) p :=
    RingHom.expChar ((traceOn (perfectClosure F Ω) A).subtype) Subtype.coe_injective p

  obtain ⟨n, z, hz⟩ := (mem_perfectClosure_iff.mp (w : perfectClosure F Ω).2)

  have hzO : z ∈ traceOn F A := by
    rw [ValuationSubring.mem_comap, hz]
    exact pow_mem (ValuationSubring.mem_comap.mp w.2) _
  obtain ⟨s, hs⟩ := exists_pow_sub_mem_maximalIdeal (traceOn F A) p n ⟨z, hzO⟩
  refine ⟨s, ?_⟩
  set ι := inclHom (traceOn F A) (traceOn (perfectClosure F Ω) A) (lies_over_perfectClosure A)
    with hιdef
  have hwz : w ^ p ^ n = ι ⟨z, hzO⟩ := by
    apply Subtype.ext
    apply (algebraMap (perfectClosure F Ω) Ω).injective
    change algebraMap _ Ω ((w : perfectClosure F Ω) ^ p ^ n) =
      algebraMap _ Ω (algebraMap F (perfectClosure F Ω) z)
    rw [map_pow, ← IsScalarTower.algebraMap_apply, hz]
    rfl
  have hpow : (w - ι s) ^ p ^ n ∈ maximalIdeal (traceOn (perfectClosure F Ω) A) := by
    rw [sub_pow_expChar_pow, hwz, ← map_pow, ← map_sub, ← neg_sub, map_neg]
    refine Submodule.neg_mem _ ?_

    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mp hs
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ hpow

theorem finite_residueField_traceOn_perfectClosure [Finite (ResidueField (traceOn F A))] :
    Finite (ResidueField (traceOn (perfectClosure F Ω) A)) :=
  Finite.of_surjective _
    (residueField_map_surjective (traceOn F A) (traceOn (perfectClosure F Ω) A)
      (lies_over_perfectClosure A) (exists_sub_inclHom_mem_maximalIdeal_perfectClosure A))

end Perfect

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem eq_top_of_forall_algebraMap_mem [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hKA : ∀ y : K, algebraMap K Ω y ∈ A) : A = ⊤ := by
  refine top_unique fun z _ => ?_
  let φ : K →+* ↥A :=
    { toFun := fun y => ⟨algebraMap K Ω y, hKA y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hzK : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral
  have hzA : IsIntegral ↥A z := by
    obtain ⟨f, hf, hfz⟩ := hzK
    refine ⟨f.map φ, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap ↥A Ω).comp φ = algebraMap K Ω := RingHom.ext fun _ => rfl
    rw [this]
    exact hfz
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := Ω)).mp hzA
  rw [← hy]
  exact y.2

theorem exists_algebraMap_eq_of_mem [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (y : K) (hy : algebraMap K Ω y ∈ A) : ∃ r : R, algebraMap R K r = y := by
  classical
  by_contra hne
  push Not at hne
  apply hAtop
  apply eq_top_of_forall_algebraMap_mem (K := K) A
  rcases ValuationRing.isInteger_or_isInteger R y with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact absurd hr (hne r)

  have hy0 : y ≠ 0 := fun h => hne 0 (by rw [h, map_zero])
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, inv_eq_zero] at hr
    exact hy0 hr
  have hrmax : r ∈ maximalIdeal R := by
    by_contra hru
    have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hru
    apply hne ↑(hu.unit⁻¹)
    have h1 : algebraMap R K ↑(hu.unit⁻¹) * algebraMap R K r = 1 := by
      rw [← map_mul, Units.inv_mul_eq_one.mpr hu.unit_spec, map_one]
    rw [hr] at h1
    calc algebraMap R K ↑(hu.unit⁻¹) = algebraMap R K ↑(hu.unit⁻¹) * y⁻¹ * y := by
          rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
      _ = y := by rw [h1, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hru
    exact (IsLocalRing.mem_maximalIdeal _).mp hrmax (hru ▸ u.isUnit)
  set ι : R →+* Ω := (algebraMap K Ω).comp (algebraMap R K) with hιdef
  have hι : ∀ r : R, ι r ∈ A := fun r => hA r
  have hιinj : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)

  have hπninv : (ι π ^ n)⁻¹ ∈ A := by
    have h1 : ι π ^ n = ι (↑u⁻¹ : R) * (algebraMap K Ω y)⁻¹ := by
      rw [← map_pow, ← map_inv₀, ← hr]
      change ι (π ^ n) = ι (↑u⁻¹ : R) * ι r
      rw [← map_mul, hru, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h1, mul_inv, inv_inv]
    refine mul_mem ?_ hy
    have h2 : (ι (↑u⁻¹ : R))⁻¹ = ι (u : R) := by
      have : ι (↑u⁻¹ : R) * ι (u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      exact (eq_inv_of_mul_eq_one_right this).symm
    rw [h2]
    exact hι u
  have hπinv : (ι π)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff] at hπninv ⊢
    rw [← inv_pow, map_pow] at hπninv
    exact (pow_le_one_iff hn).mp hπninv

  intro w
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) w
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, v, hbv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [map_div₀]
  change ι a / ι b ∈ A
  rw [div_eq_mul_inv]
  refine mul_mem (hι a) ?_
  rw [hbv, map_mul, map_pow, mul_inv, ← inv_pow]
  refine mul_mem ?_ (pow_mem hπinv m)
  have h2 : (ι (v : R))⁻¹ = ι (↑v⁻¹ : R) := by
    have : ι (v : R) * ι (↑v⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact (eq_inv_of_mul_eq_one_right this).symm
  rw [h2]
  exact hι _

def baseHom (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) :
    R →+* traceOn K A where
  toFun r := ⟨algebraMap R K r, ValuationSubring.mem_comap.mpr (hA r)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem baseHom_surjective [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤) :
    Function.Surjective (baseHom A hA) := by
  intro w
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem A hA hAtop (w : K) (ValuationSubring.mem_comap.mp w.2)
  exact ⟨r, Subtype.ext hr⟩

theorem isLocalHom_baseHom [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤) :
    IsLocalHom (baseHom A hA) := by
  constructor
  intro r hr
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hr
  obtain ⟨s, rfl⟩ := baseHom_surjective A hA hAtop w
  rw [← map_mul] at hw
  have h1 : algebraMap R K (r * s) = 1 := congrArg Subtype.val hw
  rw [← map_one (algebraMap R K)] at h1
  exact IsUnit.of_mul_eq_one s (IsFractionRing.injective R K h1)

theorem finite_residueField_traceOn_base [Algebra.IsAlgebraic K Ω] [Finite (ResidueField R)]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    (hAtop : A ≠ ⊤) : Finite (ResidueField (traceOn K A)) := by
  haveI := isLocalHom_baseHom A hA hAtop
  refine Finite.of_surjective (ResidueField.map (baseHom A hA)) fun y => ?_
  obtain ⟨w, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := baseHom_surjective A hA hAtop w
  exact ⟨residue R r, rfl⟩

theorem finite_residueField_traceOn_intermediateField [Algebra.IsAlgebraic K Ω]
    [Finite (ResidueField R)]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A)
    (hAtop : A ≠ ⊤) (F : IntermediateField K Ω) [FiniteDimensional K F] :
    Finite (ResidueField (traceOn F A)) := by
  haveI := finite_residueField_traceOn_base A hA hAtop
  have hOF : ∀ x : K, algebraMap K F x ∈ traceOn F A ↔ x ∈ traceOn K A := fun x => by
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
  letI := resAlg (traceOn K A) (traceOn F A) hOF
  haveI : FiniteDimensional (ResidueField (traceOn K A)) (ResidueField (traceOn F A)) :=
    (ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff (E := K) (F := F)
      (traceOn K A) (ι := Unit) (fun _ => traceOn F A) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ x => hOF x) (fun _ a => resAlg_algebraMap_residue (traceOn K A) (traceOn F A) hOF a)).1
      ()
  exact Module.finite_of_finite (ResidueField (traceOn K A))

theorem natCast_mem_nonunits [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (p : ℕ) (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) : (p : Ω) ∈ A.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_notMem]
  by_cases hp0 : (p : Ω) = 0
  · exact Or.inl hp0
  right
  intro hinv
  have hpK : (p : Ω) = algebraMap K Ω (p : K) := by simp
  rw [hpK, ← map_inv₀] at hinv
  obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_mem A hA hAtop _ hinv
  have hpK0 : (p : K) ≠ 0 := by
    intro h; apply hp0; rw [hpK, h, map_zero]
  have h1 : algebraMap R K ((p : R) * s) = algebraMap R K 1 := by
    rw [map_mul, hs, map_natCast, mul_inv_cancel₀ hpK0, map_one]
  have h2 : (p : R) * s = 1 := IsFractionRing.injective R K h1
  exact (IsLocalRing.mem_maximalIdeal _).mp hp (IsUnit.of_mul_eq_one s h2)

theorem charP_residueField_traceOn [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω)
    (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (F' : Type*) [Field F'] [Algebra F' Ω] : CharP (ResidueField (traceOn F' A)) p := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  change ((p : ℕ) : ResidueField (traceOn F' A)) = 0
  rw [← map_natCast (residue (traceOn F' A)) p, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  change ((p : traceOn F' A) : F') ∈ (A.comap (algebraMap F' Ω)).nonunits
  rw [mem_nonunits_comap_iff]
  simpa using natCast_mem_nonunits A hA hAtop p hp

end DVR

end P2mKcFrobDvr
p2m_reactivate "P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing.P2mKcFrobDvr"

open P2mKcFrobDvr IsLocalRing in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (F : IntermediateField K Ω) [FiniteDimensional K ↥F] :
    ∃ (d : ℕ) (φ : Ω ≃ₐ[K] Ω), 0 < d ∧ (∀ z ∈ F, φ z = z) ∧ A.IsFrobeniusAt φ (p ^ d) := by
  classical
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K

  set F' : IntermediateField F Ω := perfectClosure F Ω with hF'def
  haveI : Algebra.IsAlgebraic F' Ω := Algebra.IsAlgebraic.tower_top (K := F) F'
  haveI : Algebra.IsSeparable F' Ω := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Normal F' Ω := inferInstance
  haveI : IsGalois F' Ω := ⟨⟩

  set O : ValuationSubring F' := traceOn F' A with hOdef
  haveI : Finite (ResidueField (traceOn F A)) :=
    finite_residueField_traceOn_intermediateField A hA hAtop F
  haveI : Finite (ResidueField O) := finite_residueField_traceOn_perfectClosure A
  haveI : CharP (ResidueField O) p := charP_residueField_traceOn A hA hAtop p hp F'
  letI : Fintype (ResidueField O) := Fintype.ofFinite _
  obtain ⟨d, -, hcard⟩ := FiniteField.card (ResidueField O) p
  have hq : Nat.card (ResidueField O) = p ^ (d : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]

  have hW : ∀ x : F', algebraMap F' Ω x ∈ A ↔ x ∈ O := fun x => ValuationSubring.mem_comap.symm
  obtain ⟨σ, hσ, hfrob⟩ := exists_mem_decompositionSubgroup_forall_smul_eq_pow O A hW

  have hfixF' : ∀ x : Ω, x ∈ F' → σ x = x := fun x hx => σ.commutes ⟨x, hx⟩
  have hfixF : ∀ z : Ω, z ∈ F → σ z = z := fun z hz =>
    hfixF' z (show ((⟨z, hz⟩ : F) : Ω) ∈ F' from IntermediateField.algebraMap_mem F' ⟨z, hz⟩)
  have hfixK : ∀ k : K, σ (algebraMap K Ω k) = algebraMap K Ω k := fun k =>
    hfixF _ (F.algebraMap_mem k)
  let φ : Ω ≃ₐ[K] Ω := AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfixK
  have hφσ : ∀ x : Ω, φ x = σ x := fun _ => rfl
  have hφsymm : ∀ x : Ω, φ.symm x = σ.symm x := fun x =>
    φ.injective (by rw [AlgEquiv.apply_symm_apply, hφσ, AlgEquiv.apply_symm_apply])
  have hσA : σ • A = A := hσ
  have hφA : φ • A = A := by
    ext x
    rw [mem_smul_iff, hφsymm, ← mem_smul_iff, hσA]
  refine ⟨d, φ, d.pos, hfixF, hφA, fun x => ?_⟩
  obtain ⟨w, rfl⟩ := residue_surjective x
  rw [← hq, smul_residue_eq_pow_iff]
  have := (smul_residue_eq_pow_iff A ⟨σ, hσ⟩ w (Nat.card (ResidueField O))).mp (hfrob (residue A w))
  exact this

end S_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing (solution)
