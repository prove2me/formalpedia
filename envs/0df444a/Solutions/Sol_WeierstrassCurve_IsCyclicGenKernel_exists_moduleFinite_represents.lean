-- Prove2me | solution 1 for WeierstrassCurve.IsCyclicGenKernel.exists_moduleFinite_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6dd78d35-d580-56f1-8a50-3a9509a1da8f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents

set_option autoImplicit false

universe u

open Polynomial

namespace CycGenRepBody

noncomputable section

section lc

variable {B : Type u} [CommRing B]

def lc (n : ℤ) : ℤ := if Even n then n / 2 else n

def ed (n : ℤ) : ℕ := (n.natAbs ^ 2 - if Even n then 4 else 1) / 2

lemma natDegree_preΨ_le' (W : WeierstrassCurve B) (n : ℤ) : (W.preΨ n).natDegree ≤ ed n :=
  W.natDegree_preΨ_le n

lemma coeff_preΨ' (W : WeierstrassCurve B) (n : ℤ) : (W.preΨ n).coeff (ed n) = (lc n : B) :=
  W.coeff_preΨ n

lemma isUnit_lc {p : ℕ} (hp : p.Prime) (hpu : IsUnit (p : B)) (j : ℕ) :
    IsUnit ((lc ((p : ℤ) ^ j) : ℤ) : B) := by
  unfold lc
  by_cases he : Even ((p : ℤ) ^ j)
  · rw [if_pos he]
    obtain ⟨hpe, hj⟩ := Int.even_pow.mp he
    have hp2 : p = 2 := hp.even_iff.mp ((Int.even_coe_nat p).mp hpe)
    subst hp2
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have : ((2 : ℕ) : ℤ) ^ (i + 1) / 2 = 2 ^ i := by simp [pow_succ]
    rw [this]
    push_cast
    exact (hpu.pow i)
  · rw [if_neg he]
    push_cast
    exact hpu.pow j

end lc

section nrm

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {p : ℕ} (hp : p.Prime) (hpu : IsUnit (p : B))

noncomputable def lcUnit (j : ℕ) : Bˣ := (isUnit_lc hp hpu j).unit

lemma coe_lcUnit (j : ℕ) : ((lcUnit hp hpu j : Bˣ) : B) = ((lc ((p : ℤ) ^ j) : ℤ) : B) := rfl

variable {T : Type u} [CommRing T]

noncomputable def nrm (φ : B →+* T) (j : ℕ) : T[X] :=
  C (φ ((lcUnit hp hpu j)⁻¹ : Bˣ)) * (W.map φ).preΨ ((p : ℤ) ^ j)

lemma nrm_monic (φ : B →+* T) (j : ℕ) : (nrm W hp hpu φ j).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (ed ((p : ℤ) ^ j))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_preΨ_le' _ _)
  · rw [nrm, coeff_C_mul, coeff_preΨ', ← map_intCast φ, ← map_mul, ← coe_lcUnit hp hpu,
      Units.inv_mul, map_one]

lemma C_mul_nrm (φ : B →+* T) (j : ℕ) :
    C (φ (lcUnit hp hpu j : Bˣ)) * nrm W hp hpu φ j = (W.map φ).preΨ ((p : ℤ) ^ j) := by
  rw [nrm, ← mul_assoc, ← C_mul, ← map_mul, Units.mul_inv, map_one, C_1, one_mul]

lemma isUnit_C_lcUnit (φ : B →+* T) (j : ℕ) : IsUnit (C (φ (lcUnit hp hpu j : Bˣ))) :=
  (((lcUnit hp hpu j).isUnit.map φ).map C)

lemma map_nrm {T' : Type u} [CommRing T'] (φ : B →+* T) (σ : T →+* T') (j : ℕ) :
    (nrm W hp hpu φ j).map σ = nrm W hp hpu (σ.comp φ) j := by
  rw [nrm, nrm, Polynomial.map_mul, map_C, ← WeierstrassCurve.map_preΨ, WeierstrassCurve.map_map]
  rfl

lemma mul_preΨ_dvd_iff (φ : B →+* T) (k : ℕ) (h : T[X]) :
    h * (W.map φ).preΨ ((p : ℤ) ^ (k - 1)) ∣ (W.map φ).preΨ ((p : ℤ) ^ k) ↔
      h * nrm W hp hpu φ (k - 1) ∣ (W.map φ).preΨ ((p : ℤ) ^ k) := by
  rw [← C_mul_nrm W hp hpu φ (k - 1), mul_left_comm]
  exact (isUnit_C_lcUnit hp hpu φ (k - 1)).mul_left_dvd

lemma mul_preΨ_dvd_iff_modByMonic (φ : B →+* T) (k : ℕ) (h : T[X]) (hh : h.Monic) :
    h * (W.map φ).preΨ ((p : ℤ) ^ (k - 1)) ∣ (W.map φ).preΨ ((p : ℤ) ^ k) ↔
      (W.map φ).preΨ ((p : ℤ) ^ k) %ₘ (h * nrm W hp hpu φ (k - 1)) = 0 := by
  rw [mul_preΨ_dvd_iff, modByMonic_eq_zero_iff_dvd (hh.mul (nrm_monic W hp hpu φ (k - 1)))]

end nrm

section univ

variable (B : Type u) [CommRing B] (d : ℕ)

abbrev P : Type u := MvPolynomial (Fin d) B

noncomputable def hU : (P B d)[X] :=
  X ^ d + ∑ i : Fin d, C (MvPolynomial.X i) * X ^ (i : ℕ)

variable {B d}

lemma coeff_hU (n : ℕ) :
    (hU B d).coeff n = if hn : n < d then MvPolynomial.X ⟨n, hn⟩ else if n = d then 1 else 0 := by
  rw [hU, coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hn : n < d
  · rw [dif_pos hn, if_neg hn.ne, zero_add, Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · rintro ⟨b, hb⟩ - hne
      rw [if_neg]
      intro h
      exact hne (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hn]
    rw [Finset.sum_eq_zero, add_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg]
    intro h
    exact hn (h ▸ hb)

lemma map_hU_eq {T : Type u} [CommRing T] (ψ : P B d →+* T) (h : T[X]) (hdeg : h.natDegree ≤ d)
    (hc : h.coeff d = 1) (hX : ∀ i : Fin d, ψ (MvPolynomial.X i) = h.coeff i) : (hU B d).map ψ = h := by
  ext n
  rw [coeff_map, coeff_hU]
  by_cases hn : n < d
  · rw [dif_pos hn, hX]
  · rw [dif_neg hn]
    by_cases hnd : n = d
    · rw [if_pos hnd, map_one, hnd, hc]
    · rw [if_neg hnd, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hnd)))).symm

lemma natDegree_map_hU_le {T : Type u} [CommRing T] (ψ : P B d →+* T) : ((hU B d).map ψ).natDegree ≤ d := by
  refine (natDegree_map_le).trans ?_
  rw [hU]
  refine (natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le _) ?_)
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans ?_)
  exact i.2.le

lemma coeff_map_hU_d {T : Type u} [CommRing T] (ψ : P B d →+* T) : ((hU B d).map ψ).coeff d = 1 := by
  rw [coeff_map, coeff_hU, dif_neg (lt_irrefl d), if_pos rfl, map_one]

lemma coeff_map_hU_of_lt {T : Type u} [CommRing T] (ψ : P B d →+* T) (i : Fin d) :
    ((hU B d).map ψ).coeff i = ψ (MvPolynomial.X i) := by
  rw [coeff_map, coeff_hU, dif_pos i.2]

lemma map_hU_monic {T : Type u} [CommRing T] (ψ : P B d →+* T) : ((hU B d).map ψ).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (natDegree_map_hU_le ψ) (coeff_map_hU_d ψ)

lemma hU_monic : (hU B d).Monic := by
  simpa only [Polynomial.map_id] using map_hU_monic (RingHom.id (P B d))

lemma natDegree_hU_le : (hU B d).natDegree ≤ d := by
  simpa only [Polynomial.map_id] using natDegree_map_hU_le (RingHom.id (P B d))

lemma coeff_hU_d : (hU B d).coeff d = 1 := by
  simpa only [Polynomial.map_id] using coeff_map_hU_d (RingHom.id (P B d))

end univ

section rep

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p k : ℕ) (hp : p.Prime) (hpu : IsUnit (p : B))

def dg : ℕ := Nat.totient (p ^ k) / 2

def rels : Set (P B (dg p k)) :=
  {x | ∃ j : ℕ, x = (((W.map (algebraMap B (P B (dg p k)))).preΨ ((p : ℤ) ^ k)) %ₘ
      (hU B (dg p k) * nrm W hp hpu (algebraMap B (P B (dg p k))) (k - 1))).coeff j} ∪
  {x | ∃ a j : ℕ, 2 ≤ a ∧ a ≤ (p ^ k - 1) / 2 ∧ ¬ p ∣ a ∧
      x = (((W.map (algebraMap B (P B (dg p k)))).smulNumerator a (dg p k) (hU B (dg p k))) %ₘ
        hU B (dg p k)).coeff j}

def relI : Ideal (P B (dg p k)) := Ideal.span (rels W p k hp hpu)

abbrev Crep : Type u := P B (dg p k) ⧸ relI W p k hp hpu

noncomputable def hUniv : (Crep W p k hp hpu)[X] :=
  (hU B (dg p k)).map (Ideal.Quotient.mk (relI W p k hp hpu))

lemma algebraMap_Crep :
    algebraMap B (Crep W p k hp hpu) = (Ideal.Quotient.mk (relI W p k hp hpu)).comp (algebraMap B (P B (dg p k))) :=
  rfl

noncomputable def rem₁ : (P B (dg p k))[X] :=
  ((W.map (algebraMap B (P B (dg p k)))).preΨ ((p : ℤ) ^ k)) %ₘ
    (hU B (dg p k) * nrm W hp hpu (algebraMap B (P B (dg p k))) (k - 1))

noncomputable def rem₂ (a : ℕ) : (P B (dg p k))[X] :=
  ((W.map (algebraMap B (P B (dg p k)))).smulNumerator a (dg p k) (hU B (dg p k))) %ₘ hU B (dg p k)

lemma rem₁_def : rem₁ W p k hp hpu = ((W.map (algebraMap B (P B (dg p k)))).preΨ ((p : ℤ) ^ k)) %ₘ
    (hU B (dg p k) * nrm W hp hpu (algebraMap B (P B (dg p k))) (k - 1)) := rfl

lemma rem₂_def (a : ℕ) : rem₂ W p k a =
    ((W.map (algebraMap B (P B (dg p k)))).smulNumerator a (dg p k) (hU B (dg p k))) %ₘ hU B (dg p k) := rfl

lemma mem_rels_iff (x : P B (dg p k)) : x ∈ rels W p k hp hpu ↔
    (∃ j : ℕ, x = (rem₁ W p k hp hpu).coeff j) ∨
      ∃ a j : ℕ, 2 ≤ a ∧ a ≤ (p ^ k - 1) / 2 ∧ ¬ p ∣ a ∧ x = (rem₂ W p k a).coeff j := Iff.rfl

variable {T : Type u} [CommRing T] (ψ : P B (dg p k) →+* T)

lemma map_rem₁ : (rem₁ W p k hp hpu).map ψ =
    ((W.map (ψ.comp (algebraMap B (P B (dg p k))))).preΨ ((p : ℤ) ^ k)) %ₘ
      ((hU B (dg p k)).map ψ * nrm W hp hpu (ψ.comp (algebraMap B (P B (dg p k)))) (k - 1)) := by
  rw [rem₁_def, map_modByMonic ψ (hU_monic.mul (nrm_monic W hp hpu _ _)), Polynomial.map_mul,
    map_nrm, ← WeierstrassCurve.map_preΨ, WeierstrassCurve.map_map]

lemma map_rem₂ (a : ℕ) : (rem₂ W p k a).map ψ =
    ((W.map (ψ.comp (algebraMap B (P B (dg p k))))).smulNumerator a (dg p k) ((hU B (dg p k)).map ψ)) %ₘ
      (hU B (dg p k)).map ψ := by
  rw [rem₂_def, map_modByMonic ψ hU_monic, ← WeierstrassCurve.smulNumerator_map, WeierstrassCurve.map_map]

lemma isCyclicGenKernel_map_iff :
    (W.map (ψ.comp (algebraMap B (P B (dg p k))))).IsCyclicGenKernel p k ((hU B (dg p k)).map ψ) ↔
      ∀ x ∈ rels W p k hp hpu, ψ x = 0 := by
  have hmon : ((hU B (dg p k)).map ψ).Monic := map_hU_monic ψ
  constructor
  · intro hcg x hx
    rcases (mem_rels_iff W p k hp hpu x).mp hx with ⟨j, rfl⟩ | ⟨a, j, ha, ha', hpa, rfl⟩
    · rw [← coeff_map, map_rem₁]
      have h0 := (mul_preΨ_dvd_iff_modByMonic W hp hpu _ k _ hmon).mp hcg.mul_preΨ_dvd
      rw [h0, coeff_zero]
    · rw [← coeff_map, map_rem₂]
      have h0 : ((W.map (ψ.comp (algebraMap B (P B (dg p k))))).smulNumerator a (dg p k)
          ((hU B (dg p k)).map ψ)) %ₘ (hU B (dg p k)).map ψ = 0 :=
        (modByMonic_eq_zero_iff_dvd hmon).mpr (hcg.dvd_smulNumerator a ha ha' hpa)
      rw [h0, coeff_zero]
  · intro hz
    refine
      { natDegree_le := natDegree_map_hU_le ψ
        coeff_eq_one := coeff_map_hU_d ψ
        mul_preΨ_dvd := ?_
        dvd_smulNumerator := ?_ }
    · rw [mul_preΨ_dvd_iff_modByMonic W hp hpu _ k _ hmon, ← map_rem₁]
      ext j
      rw [coeff_map, coeff_zero]
      exact hz _ ((mem_rels_iff W p k hp hpu _).mpr (Or.inl ⟨j, rfl⟩))
    · intro a ha ha' hpa
      change (hU B (dg p k)).map ψ ∣
        (W.map (ψ.comp (algebraMap B (P B (dg p k))))).smulNumerator a (dg p k) ((hU B (dg p k)).map ψ)
      rw [← modByMonic_eq_zero_iff_dvd hmon, ← map_rem₂]
      ext j
      rw [coeff_map, coeff_zero]
      exact hz _ ((mem_rels_iff W p k hp hpu _).mpr (Or.inr ⟨a, j, ha, ha', hpa, rfl⟩))

lemma isCyclicGenKernel_hUniv :
    (W.map (algebraMap B (Crep W p k hp hpu))).IsCyclicGenKernel p k (hUniv W p k hp hpu) := by
  rw [algebraMap_Crep]
  refine (isCyclicGenKernel_map_iff W p k hp hpu (Ideal.Quotient.mk (relI W p k hp hpu))).mpr ?_
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hx)

lemma isIntegral_mk_X (i : Fin (dg p k)) :
    IsIntegral B (Ideal.Quotient.mk (relI W p k hp hpu) (MvPolynomial.X i)) := by
  have hcoeff : (hUniv W p k hp hpu).coeff i = Ideal.Quotient.mk (relI W p k hp hpu) (MvPolynomial.X i) :=
    coeff_map_hU_of_lt _ i
  rw [← hcoeff]

  have hcg := isCyclicGenKernel_hUniv W p k hp hpu
  refine Polynomial.isIntegral_coeff_of_dvd (nrm W hp hpu (RingHom.id B) k) (hUniv W p k hp hpu)
    (nrm_monic W hp hpu _ _) (map_hU_monic _) ?_ i
  rw [map_nrm, RingHom.comp_id]
  have h1 : hUniv W p k hp hpu ∣ (W.map (algebraMap B (Crep W p k hp hpu))).preΨ ((p : ℤ) ^ k) :=
    dvd_trans (dvd_mul_right _ _) hcg.mul_preΨ_dvd
  exact dvd_trans h1 (Dvd.intro_left _ rfl)

lemma algebra_isIntegral : Algebra.IsIntegral B (Crep W p k hp hpu) := by
  constructor
  intro c
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : Ideal.Quotient.mk (relI W p k hp hpu) (MvPolynomial.C a) = algebraMap B (Crep W p k hp hpu) a := rfl
    rw [this]
    exact isIntegral_algebraMap
  | add q r hq hr => rw [map_add]; exact hq.add hr
  | mul_X q i hq => rw [map_mul]; exact hq.mul (isIntegral_mk_X W p k hp hpu i)

lemma finiteType : Algebra.FiniteType B (Crep W p k hp hpu) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B (relI W p k hp hpu))
    (Ideal.Quotient.mkₐ_surjective B _)

lemma moduleFinite : Module.Finite B (Crep W p k hp hpu) :=
  haveI := algebra_isIntegral W p k hp hpu
  haveI := finiteType W p k hp hpu
  Algebra.IsIntegral.finite

lemma represents (T : Type u) [CommRing T] (φ : B →+* T) (h : T[X]) :
    (W.map φ).IsCyclicGenKernel p k h ↔
      ∃! ψ : Crep W p k hp hpu →+* T, ψ.comp (algebraMap B (Crep W p k hp hpu)) = φ ∧
        (hUniv W p k hp hpu).map ψ = h := by
  constructor
  · intro hh

    let ψ₀ : P B (dg p k) →+* T := MvPolynomial.eval₂Hom φ (fun i => h.coeff i)
    have hψ₀C : ψ₀.comp (algebraMap B (P B (dg p k))) = φ := by
      ext b; exact MvPolynomial.eval₂Hom_C _ _ b
    have hmap : (hU B (dg p k)).map ψ₀ = h :=
      map_hU_eq ψ₀ h hh.natDegree_le hh.coeff_eq_one (fun i => MvPolynomial.eval₂Hom_X' _ _ i)
    have hker : ∀ x ∈ relI W p k hp hpu, ψ₀ x = 0 := by
      intro x hx
      have hle : relI W p k hp hpu ≤ RingHom.ker ψ₀ := by
        rw [relI, Ideal.span_le]
        intro y hy
        rw [SetLike.mem_coe, RingHom.mem_ker]
        refine (isCyclicGenKernel_map_iff W p k hp hpu ψ₀).mp ?_ y hy
        rw [hψ₀C, hmap]
        exact hh
      exact hle hx
    let ψ : Crep W p k hp hpu →+* T := Ideal.Quotient.lift _ ψ₀ hker
    have hψmk : ψ.comp (Ideal.Quotient.mk _) = ψ₀ := Ideal.Quotient.lift_comp_mk _ _ _
    refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
    · rw [algebraMap_Crep, ← RingHom.comp_assoc, hψmk, hψ₀C]
    · rw [hUniv, Polynomial.map_map, hψmk, hmap]
    · rintro ψ' ⟨h1, h2⟩
      apply Ideal.Quotient.ringHom_ext
      rw [hψmk]
      apply MvPolynomial.ringHom_ext
      · intro b
        change (ψ'.comp ((Ideal.Quotient.mk (relI W p k hp hpu)).comp (algebraMap B (P B (dg p k))))) b = _
        rw [← algebraMap_Crep, h1, ← hψ₀C]
        rfl
      · intro i
        rw [RingHom.comp_apply, ← coeff_map_hU_of_lt (Ideal.Quotient.mk (relI W p k hp hpu)) i]
        change ψ' ((hUniv W p k hp hpu).coeff i) = _
        rw [← coeff_map, h2, MvPolynomial.eval₂Hom_X']
  · rintro ⟨ψ, ⟨h1, h2⟩, -⟩
    have := (isCyclicGenKernel_hUniv W p k hp hpu).map _ ψ
    rwa [WeierstrassCurve.map_map, h1, h2] at this

end rep

end

theorem main
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p k : ℕ) [Fact p.Prime] (hpk : 3 ≤ p ^ k)
    (hu : IsUnit ((p : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsCyclicGenKernel p k hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsCyclicGenKernel p k h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by
  have hp : p.Prime := Fact.out
  have hpu : IsUnit (p : B) := isUnit_of_mul_isUnit_left hu
  exact ⟨Crep W p k hp hpu, inferInstance, inferInstance, moduleFinite W p k hp hpu, hUniv W p k hp hpu,
    isCyclicGenKernel_hUniv W p k hp hpu, represents W p k hp hpu⟩

end CycGenRepBody

theorem solution
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p k : ℕ) [Fact p.Prime] (hpk : 3 ≤ p ^ k)
    (hu : IsUnit ((p : B) * W.Δ)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsCyclicGenKernel p k hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsCyclicGenKernel p k h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h :=
  CycGenRepBody.main W p k hpk hu

end S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents
end P2MW
export P2MW.S_WeierstrassCurve_IsCyclicGenKernel_exists_moduleFinite_represents (solution)
