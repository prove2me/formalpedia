-- Prove2me | solution 1 for Submodule.forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2e6eef2b-68fb-5d93-9c1c-2135479199f6

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace AwayConjModule

section Places

abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem pgen_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (pgen w).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator w

def place (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem primesEquiv_place (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place p hp) = ⟨p, hp⟩ := by
  simp [place]

theorem pgen_place (p : ℕ) (hp : p.Prime) : pgen (place p hp) = p :=
  congrArg Subtype.val (primesEquiv_place p hp)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem pgen_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : pgen v = p :=
  (Nat.prime_dvd_prime_iff_eq (pgen_prime v) hp).1 ((natCast_mem_asIdeal_iff v p).1 hv)

theorem pgen_injective : Function.Injective pgen := by
  intro w w' h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = w.valuation ℚ c := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

theorem valuation_natCast_eq_one_of_not_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  refine (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 ?_
  rwa [natCast_mem_asIdeal_iff]

theorem mem_integers_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ w.adicCompletionIntegers ℚ ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem zpow_natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : ¬ pgen w ∣ n) (i : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ) ^ i) ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_integers_iff, valued_algebraMap, map_zpow₀, valuation_natCast_eq_one_of_not_dvd w hn, one_zpow]

theorem cst_zpow' (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) (n : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) (x ^ n) = algebraMap ℚ (w.adicCompletion ℚ) x ^ n :=
  map_zpow₀ _ x n

theorem intCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℤ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := intCast_mem _ t

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) :
    (t : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := natCast_mem _ t

end Places

section Boxes

variable {a b : ℚ} {O : Submodule ℤ ℍ[ℚ, a, b]}

theorem tmul_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox O w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : ℍ[ℚ, a, b]} (hz : z ∈ O) (w : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox O w :=
  tmul_mem_localBox hz w (one_mem _)

end Boxes

section LocalGlobal

variable {a b : ℚ}

open QuaternionAlgebra

def extendScalar (w : HeightOneSpectrum (𝓞 ℚ)) (f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →ₗ[ℚ] w.adicCompletion ℚ :=
  (TensorProduct.lid ℚ (w.adicCompletion ℚ)).toLinearMap ∘ₗ f.rTensor (w.adicCompletion ℚ)

theorem extendScalar_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (f : ℍ[ℚ, a, b] →ₗ[ℚ] ℚ) (x : ℍ[ℚ, a, b])
    (y : w.adicCompletion ℚ) : extendScalar w f (x ⊗ₜ[ℚ] y) = f x • y := by
  simp [extendScalar]

theorem extendScalar_coord_mem_integers {R : Submodule ℤ ℍ[ℚ, a, b]}
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBR : Submodule.span ℤ (Set.range B) = R)
    (w : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 4) {t : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (ht : t ∈ Submodule.localBox R w) :
    extendScalar w (B.coord i) t ∈ w.adicCompletionIntegers ℚ := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    rw [extendScalar_tmul, Module.Basis.coord_apply]
    rw [← hBR] at hz
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ B z).1 hz i
    rw [← hm, algebraMap_smul]
    exact zsmul_mem hc m
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem exists_natCast_smul_mem_of_tmul_one_mem_localBox {R : Submodule ℤ ℍ[ℚ, a, b]}
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBR : Submodule.span ℤ (Set.range B) = R)
    (w : HeightOneSpectrum (𝓞 ℚ)) {x : ℍ[ℚ, a, b]}
    (hx : x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) :
    ∃ n : ℕ, ¬ pgen w ∣ n ∧ (n : ℚ) • x ∈ R := by
  have hden : ∀ i, ¬ pgen w ∣ (B.repr x i).den := by
    intro i hdvd
    have hint := extendScalar_coord_mem_integers B hBR w i hx
    rw [extendScalar_tmul, Module.Basis.coord_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      Algebra.smul_def, mul_one, valued_algebraMap, Rat.valuation_le_one_iff_den] at hint
    exact hint ((natCast_mem_asIdeal_iff w _).2 hdvd)
  refine ⟨∏ i, (B.repr x i).den, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (pgen_prime w).prime _).1 h
    exact hden i hi
  · rw [← hBR, Module.Basis.mem_span_iff_repr_mem]
    intro i
    refine ⟨(∏ j ∈ Finset.univ.erase i, ((B.repr x j).den : ℤ)) * (B.repr x i).num, ?_⟩
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
    simp

theorem exists_pow_smul_mem {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) {r : ℕ} (hr : r.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (r : 𝓞 ℚ) ∈ v.asIdeal) {x : ℍ[ℚ, a, b]}
    (hx : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      x ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) :
    ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • x ∈ R := by
  obtain ⟨B, -, hBR⟩ := hR.exists_basis_span_eq
  have hgen : pgen v = r := pgen_eq_of_prime_mem hr v hv
  have step : ∀ p : ℕ, p.Prime → p ≠ r → ∃ n : ℕ, ¬ p ∣ n ∧ (n : ℚ) • x ∈ R := by
    intro p hp hpr
    have hw : place p hp ≠ v := by
      intro h; apply hpr; rw [← pgen_place p hp, h, hgen]
    obtain ⟨n, hn, hnx⟩ := exists_natCast_smul_mem_of_tmul_one_mem_localBox B hBR (place p hp) (hx _ hw)
    rw [pgen_place] at hn
    exact ⟨n, hn, hnx⟩
  let I : Ideal ℤ := R.comap (LinearMap.toSpanSingleton ℤ ℍ[ℚ, a, b] x)
  have hI : ∀ n : ℤ, n ∈ I ↔ (n : ℚ) • x ∈ R := by
    intro n
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Int.cast_smul_eq_zsmul ℚ]
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = Submodule.IsPrincipal.generator I := ⟨_, rfl⟩
  have hdI : d ∈ I := hd ▸ Submodule.IsPrincipal.generator_mem I
  have hdvd : ∀ n : ℤ, n ∈ I → d ∣ n := fun n hn =>
    hd ▸ (Submodule.IsPrincipal.mem_iff_generator_dvd I).1 hn
  have hprime : ∀ {p : ℕ}, p.Prime → p ∣ d.natAbs → p = r := by
    intro p hp hpd
    by_contra hpr
    obtain ⟨n, hn, hnx⟩ := step p hp hpr
    apply hn
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    have h2 : (p : ℤ) ∣ (n : ℤ) := (Int.natCast_dvd.2 hpd).trans h1
    exact Int.natCast_dvd_natCast.1 h2
  have hd0 : d.natAbs ≠ 0 := by
    obtain ⟨p, hp, hpr⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ r := by
      by_cases h : r = 2
      · exact ⟨3, Nat.prime_three, by omega⟩
      · exact ⟨2, Nat.prime_two, fun e => h e.symm⟩
    obtain ⟨n, hn, hnx⟩ := step p hp hpr
    intro hd0
    have h1 : d ∣ (n : ℤ) := hdvd n ((hI n).2 (by exact_mod_cast hnx))
    rw [Int.natAbs_eq_zero.1 hd0, zero_dvd_iff, Int.natCast_eq_zero] at h1
    exact hn (h1 ▸ dvd_zero p)
  refine ⟨d.natAbs.primeFactorsList.length, ?_⟩
  rw [← Nat.eq_prime_pow_of_unique_prime_dvd hd0 hprime]
  have hmem : ((d.natAbs : ℤ) : ℚ) • x ∈ R := by
    rw [← hI]
    rcases Int.natAbs_eq d with h | h
    · rw [← h]; exact hdI
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this]; exact I.neg_mem hdI
  exact_mod_cast hmem

end LocalGlobal

section Idele

variable {a b : ℚ}

open QuaternionAlgebra

abbrev Hhat (a b : ℚ) : Type := ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem evalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]
  rfl

theorem evalAt_diagonal_mul (w : HeightOneSpectrum (𝓞 ℚ)) (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (Hhat a b)ˣ)
    (hg : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : Hhat a b) = 1) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g : (Hhat a b)ˣ) : Hhat a b) =
      (γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Units.val_mul, map_mul, hg, mul_one, Submodule.val_finiteIdeleDiagonal_apply, evalAt_tmul_one]

theorem evalAt_diagonal_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (Hhat a b)ˣ)
    (hg : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : Hhat a b) = 1) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g)⁻¹ : (Hhat a b)ˣ) : Hhat a b) =
      ((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  have hginv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (Hhat a b)ˣ) : Hhat a b) = 1 := by
    have h := congrArg (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w) g.mul_inv
    rw [map_mul, map_one, hg, one_mul] at h
    exact h
  rw [mul_inv_rev, Units.val_mul, map_mul, hginv, one_mul, ← map_inv,
    Submodule.val_finiteIdeleDiagonal_apply, evalAt_tmul_one]

theorem diag_conj_tmul (γ₀ : (ℍ[ℚ, a, b])ˣ) (z : ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
        (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
      ((γ₀ : ℍ[ℚ, a, b]) * z * ((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

theorem diag_inv_conj_tmul (γ₀ : (ℍ[ℚ, a, b])ˣ) (z : ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
        ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
      (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * (γ₀ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

end Idele

section Main

variable {a b : ℚ}

open QuaternionAlgebra

theorem main (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (Hhat a b)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : Hhat a b) = 1)
    (hconj : Submodule.conjByFiniteIdele R' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g) = R) :
    (∀ x : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) * ((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R') ∧
    (∀ y : ↥R', ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) * ((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R) := by

  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      x' ∈ Submodule.localBox R w ↔ ∃ y' ∈ Submodule.localBox R' w,
        x' = ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * y' *
          (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
    intro w hw x'
    have h := Submodule.mem_localBox_conjByFiniteIdele_iff R' hR'.fg hR'.spanTop
      (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g) w x'
    rw [hconj, evalAt_diagonal_mul w γ₀ g (hg w hw), evalAt_diagonal_mul_inv w γ₀ g (hg w hw)] at h
    exact h
  refine ⟨fun x => ?_, fun y => ?_⟩
  ·
    refine exists_pow_smul_mem hR' hr v hv fun w hw => ?_
    obtain ⟨y', hy', hxy'⟩ := (hloc w hw _).1 (tmul_one_mem_localBox x.2 w)
    have key : (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) * (γ₀ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ]
        (1 : w.adicCompletion ℚ) = y' := by
      rw [← diag_inv_conj_tmul, hxy']
      have h1 : (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
          ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = 1 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.inv_mul, Algebra.TensorProduct.one_def]
      calc (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
            (((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * y' *
              (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) *
            ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))
          = ((((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
              ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) * y' *
            ((((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
              ((γ₀ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) := by
            simp only [mul_assoc]
        _ = y' := by rw [h1, one_mul, mul_one]
    rw [key]
    exact hy'
  ·
    refine exists_pow_smul_mem hR hr v hv fun w hw => ?_
    rw [← diag_conj_tmul]
    exact (hloc w hw _).2 ⟨_, tmul_one_mem_localBox y.2 w, rfl⟩

end Main

end AwayConjModule

end

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (R R' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hR' : IsOrder R')
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (γ₀ : (ℍ[ℚ, a, b])ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hconj : Submodule.conjByFiniteIdele R' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀ * g) = R) :
    (∀ x : ↥R, ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) * ((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R') ∧
    (∀ y : ↥R', ∃ K : ℕ,
      ((r ^ K : ℕ) : ℚ) • (((γ₀ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) * ((γ₀⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ∈ R) :=
  AwayConjModule.main R R' hR hR' r Fact.out v hv γ₀ g hg hconj

end S_Submodule_forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal
end P2MW
export P2MW.S_Submodule_forall_exists_pow_smul_conj_mem_of_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_mem_asIdeal (solution)
