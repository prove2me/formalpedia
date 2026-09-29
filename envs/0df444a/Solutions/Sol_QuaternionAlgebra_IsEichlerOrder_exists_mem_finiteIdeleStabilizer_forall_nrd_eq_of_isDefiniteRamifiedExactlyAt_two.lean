-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d8136e3e-71a7-550c-85de-6be3aac2ad44

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace LNCC2

section NrdAlgebra

variable {K : Type*} [CommRing K] {c₁ c₃ : K}

theorem nrd_mul' (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul' (r : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (r • x) = r ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

theorem sq_sub_trd_smul_add_nrd (x : ℍ[K, c₁, c₃]) :
    x * x - QuaternionAlgebra.trd x • x + QuaternionAlgebra.nrd x • (1 : ℍ[K, c₁, c₃]) = 0 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

end NrdAlgebra

section DetNrd

variable {K : Type*} [Field K] {c₁ c₃ : K}

theorem mat_sq_sub_trace_smul_add_det (A : Matrix (Fin 2) (Fin 2) K) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem det_eq_nrd_of_ringHom (θ : ℍ[K, c₁, c₃] →+* Matrix (Fin 2) (Fin 2) K)
    (hθ : ∀ r : K, θ (r • (1 : ℍ[K, c₁, c₃])) = r • (1 : Matrix (Fin 2) (Fin 2) K))
    (hinj : Function.Injective θ) (y : ℍ[K, c₁, c₃]) :
    (θ y).det = QuaternionAlgebra.nrd y := by
  have hsmul : ∀ (r : K) (z : ℍ[K, c₁, c₃]), θ (r • z) = r • θ z := fun r z => by
    rw [show r • z = (r • (1 : ℍ[K, c₁, c₃])) * z by rw [smul_mul_assoc, one_mul], map_mul, hθ,
      smul_mul_assoc, one_mul]
  set A := θ y with hA
  have h1 : A * A - QuaternionAlgebra.trd y • A + QuaternionAlgebra.nrd y • (1 : Matrix (Fin 2) (Fin 2) K)
      = 0 := by
    have := congrArg θ (sq_sub_trd_smul_add_nrd y)
    rwa [map_zero, map_add, map_sub, map_mul, hsmul, hsmul, map_one] at this
  have h2 := mat_sq_sub_trace_smul_add_det A
  have h3 : (A.trace - QuaternionAlgebra.trd y) • A =
      (A.det - QuaternionAlgebra.nrd y) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := sub_eq_zero.2 (h1.trans h2.symm)
    rw [sub_smul, sub_smul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    convert this using 1
    abel
  by_cases ht : A.trace = QuaternionAlgebra.trd y
  · rw [ht, sub_self, zero_smul] at h3
    have := congrFun (congrFun h3.symm 0) 0
    simp at this
    exact sub_eq_zero.1 this
  · have hne : A.trace - QuaternionAlgebra.trd y ≠ 0 := sub_ne_zero.2 ht
    set κ := (A.det - QuaternionAlgebra.nrd y) / (A.trace - QuaternionAlgebra.trd y) with hκ
    have hAκ : A = κ • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have := congrArg (fun M => (A.trace - QuaternionAlgebra.trd y)⁻¹ • M) h3
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      rw [this, hκ, div_eq_inv_mul]
    have hy : y = κ • (1 : ℍ[K, c₁, c₃]) := hinj (by rw [hθ, ← hAκ])
    have hdet : A.det = κ ^ 2 := by
      rw [hAκ, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    rw [hdet, hy, nrd_smul', QuaternionAlgebra.nrd_one, mul_one]

end DetNrd

section Places

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_mem_asIdeal (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal :=
  (natCast_mem_asIdeal_iff w _).2 dvd_rfl

theorem natGenerator_eq_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) {q : ℕ} (hq : q.Prime)
    (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : Rat.HeightOneSpectrum.natGenerator w = q := by
  rw [natCast_mem_asIdeal_iff] at hw
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp hw

theorem one_notMem_asIdeal (w : HeightOneSpectrum (𝓞 ℚ)) : ((1 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [Nat.cast_one]
  exact w.isPrime.one_notMem

theorem natCast_adicCompletion_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (w.adicCompletion ℚ)) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

end Places

section Hensel

open Polynomial

theorem padicInt_exists_natCast_mul_sq_eq {p : ℕ} [Fact p.Prime] (hp : p = 2) (E : ℤ_[p])
    (hE : ‖E‖ = 1) :
    ∃ (m : ℕ) (z : ℤ_[p]), 0 < m ∧ (m : ℤ_[p]) * z ^ 2 = E := by
  subst hp
  set m : ℕ := E.appr 3 with hm

  have happr : E - (m : ℤ_[2]) ∈ (Ideal.span {(2 : ℤ_[2]) ^ 3} : Ideal ℤ_[2]) := by
    have := PadicInt.appr_spec 3 E
    exact_mod_cast this
  have hle : ‖E - (m : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (E - (m : ℤ_[2])) 3).2 happr
    exact_mod_cast this
  have hlt1 : ‖E - (m : ℤ_[2])‖ < 1 := lt_of_le_of_lt hle (by norm_num)

  have hm1 : ‖(m : ℤ_[2])‖ = 1 := by
    have hmle : ‖(m : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    by_contra hne
    have hlt : ‖(m : ℤ_[2])‖ < 1 := lt_of_le_of_ne hmle hne
    have : ‖E‖ < 1 := by
      have h := PadicInt.nonarchimedean (E - (m : ℤ_[2])) (m : ℤ_[2])
      rw [sub_add_cancel] at h
      exact lt_of_le_of_lt h (max_lt hlt1 hlt)
    rw [hE] at this
    exact lt_irrefl _ this
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, norm_zero] at hm1
    exact zero_ne_one hm1
  have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
  set F : Polynomial ℤ_[2] := C (m : ℤ_[2]) * X ^ 2 - C E with hF
  have hFa : Polynomial.aeval (1 : ℤ_[2]) F = (m : ℤ_[2]) - E := by
    simp [hF]
  have hF'a : Polynomial.aeval (1 : ℤ_[2]) (derivative F) = ((2 : ℕ) : ℤ_[2]) * (m : ℤ_[2]) := by
    simp [hF]
    ring
  have hnorm : ‖Polynomial.aeval (1 : ℤ_[2]) F‖ < ‖Polynomial.aeval (1 : ℤ_[2]) (derivative F)‖ ^ 2 := by
    rw [hFa, hF'a, norm_mul, h2, hm1, mul_one, ← norm_neg, neg_sub]
    refine lt_of_le_of_lt hle ?_
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨m, z, Nat.pos_of_ne_zero hm0, ?_⟩
  have : Polynomial.aeval z F = (m : ℤ_[2]) * z ^ 2 - E := by simp [hF]
  rw [this] at hz
  exact sub_eq_zero.1 hz

end Hensel

section LocalUnit

theorem exists_natCast_mul_sq_eq_of_valued_eq_one (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : ((2 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) (ε : w.adicCompletion ℚ) (hε : Valued.v ε = 1) :
    ∃ (m : ℕ) (s : w.adicCompletion ℚ), 0 < m ∧
      algebraMap ℚ (w.adicCompletion ℚ) (m : ℚ) * s ^ 2 = ε := by
  set p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w with hp
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  have hp2 : (p : ℕ) = 2 := natGenerator_eq_of_mem w Nat.prime_two hw
  have hεmem : ε ∈ w.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hε.le
  have hε0 : ε ≠ 0 := fun h => by rw [h, map_zero] at hε; exact zero_ne_one hε
  have hεinvmem : ε⁻¹ ∈ w.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hε, inv_one]
  set εi : w.adicCompletionIntegers ℚ := ⟨ε, hεmem⟩ with hεi
  have hunit : IsUnit εi := by
    refine IsUnit.of_mul_eq_one ⟨ε⁻¹, hεinvmem⟩ ?_
    apply Subtype.ext
    change ε * ε⁻¹ = 1
    exact mul_inv_cancel₀ hε0
  let ι : w.adicCompletionIntegers ℚ ≃+* ℤ_[p] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) w).toRingEquiv
  set E : ℤ_[p] := ι εi with hEdef
  have hE : ‖E‖ = 1 := PadicInt.isUnit_iff.1 (hunit.map ι)
  obtain ⟨m, z, hm, hz⟩ := padicInt_exists_natCast_mul_sq_eq hp2 E hE
  refine ⟨m, ((ι.symm z : w.adicCompletionIntegers ℚ) : w.adicCompletion ℚ), hm, ?_⟩
  have hz' : ((m : w.adicCompletionIntegers ℚ)) * (ι.symm z) ^ 2 = εi := by
    apply ι.injective
    rw [map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply, hz]
  have := congrArg (fun t : w.adicCompletionIntegers ℚ => (t : w.adicCompletion ℚ)) hz'
  rw [show ((εi : w.adicCompletion ℚ)) = ε from rfl] at this
  rw [← this]
  push_cast
  rfl

end LocalUnit

section Coord

variable {a b : ℚ}

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

theorem IsCoord.one_tmul {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (r : w.adicCompletion ℚ) :
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • 1 := by
  rw [hφ]
  congr 1

theorem IsCoord.nrd_tmul {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : ℍ[ℚ, a, b]) (s : w.adicCompletion ℚ) :
    QuaternionAlgebra.nrd (φ (γ ⊗ₜ[ℚ] s)) =
      s ^ 2 * algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd γ) := by
  rw [hφ, nrd_smul', QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_add, map_sub, map_mul, map_pow]

theorem IsCoord.nrd_eq_det {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ)
    (ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hψ : ∀ r : w.adicCompletion ℚ,
      ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    QuaternionAlgebra.nrd (φ x) = (ψ x).det := by
  set θ : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] →+*
      Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) := ψ.toRingHom.comp φ.symm.toRingHom with hθ
  have hθ1 : ∀ r : w.adicCompletion ℚ, θ (r • 1) = r • 1 := fun r => by
    have h1 : φ.symm (r • 1) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r := by
      rw [RingEquiv.symm_apply_eq, hφ.one_tmul]
    simp only [hθ, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply, h1, hψ]
  have hinj : Function.Injective θ := by
    simp only [hθ, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact ψ.injective.comp φ.symm.injective
  have := det_eq_nrd_of_ringHom θ hθ1 hinj (φ x)
  rw [← this]
  simp [hθ]

end Coord

section Boxes

variable {a b : ℚ}

theorem mem_localBox_inf_iff {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (h₁ : QuaternionAlgebra.IsOrder Λ₁) (h₂ : QuaternionAlgebra.IsOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ↔ x ∈ Submodule.localBox Λ₁ v ∧ x ∈ Submodule.localBox Λ₂ v := by
  rw [Submodule.localBox_inf Λ₁ Λ₂ h₁.fg h₁.spanTop h₂.fg h₂.spanTop v, AddSubgroup.mem_inf]

variable {K : Type*} [Field K]

theorem units_conj_conj (u : (Matrix (Fin 2) (Fin 2) K)ˣ) (D : Matrix (Fin 2) (Fin 2) K) :
    ((u⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) *
      ((u : Matrix (Fin 2) (Fin 2) K) * D * ((u⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K)) *
      (u : Matrix (Fin 2) (Fin 2) K) = D := by
  rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]

theorem diagonal_entries_mem (S : ValuationSubring K) (d : Fin 2 → K) (hd : ∀ i, d i ∈ S) (i j : Fin 2) :
    Matrix.diagonal d i j ∈ S := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact S.zero_mem

end Boxes

section Split

variable {a b : ℚ}

theorem exists_local_unit_split {q' : ℕ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal)
    (ε : v.adicCompletion ℚ) (hε : Valued.v ε = 1) :
    ∃ x x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧ x' ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧
      x * x' = 1 ∧ x' * x = 1 ∧
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        IsCoord a b v φ → QuaternionAlgebra.nrd (φ x) = ε := by
  classical

  have hΛ₁E : QuaternionAlgebra.IsEichlerOrder Λ₁ 1 :=
    ⟨Λ₁, Λ₁, hΛ₁, hΛ₁, (inf_idem Λ₁).symm, AddSubgroup.relIndex_self _⟩
  obtain ⟨ψ, hψ1, -⟩ := QuaternionAlgebra.IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem
    hdef hΛ₁E v hq'v (one_notMem_asIdeal v)

  set ℓ : ℕ := Rat.HeightOneSpectrum.natGenerator v with hℓdef
  have hℓ : ℓ.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal := natGenerator_mem_asIdeal v
  obtain ⟨e, ⟨h, hΛ₁v, hΛ₂v⟩, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
      hΛ₁ hΛ₂ v ℓ hℓ hℓv ψ hψ1

  have hε0 : ε ≠ 0 := fun h0 => by rw [h0, map_zero] at hε; exact zero_ne_one hε
  have hεmem : ε ∈ v.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hε.le
  have hεinvmem : ε⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hε, inv_one]
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![ε, 1] with hD
  set D' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![ε⁻¹, 1] with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hε0]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hε0]
  set Du : (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ˣ := ⟨D, D', hDD', hD'D⟩ with hDu
  set U : (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ˣ := h * Du * h⁻¹ with hU
  have hUval : (U : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * D * ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [hU, Units.val_mul, Units.val_mul]
  have hUinv : ((U⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ˣ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * D' * ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [hU, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, mul_assoc]
    rfl
  set x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ := ψ.symm (U : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hx
  set x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ :=
    ψ.symm ((U⁻¹ : (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ˣ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hx'
  have hψx : ψ x = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * D * ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [hx, RingEquiv.apply_symm_apply, hUval]
  have hψx' : ψ x' = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * D' * ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    rw [hx', RingEquiv.apply_symm_apply, hUinv]

  have hDmem : ∀ i, (![ε, 1] : Fin 2 → v.adicCompletion ℚ) i ∈ v.adicCompletionIntegers ℚ := by
    intro i; fin_cases i
    · exact hεmem
    · exact one_mem _
  have hD'mem : ∀ i, (![ε⁻¹, 1] : Fin 2 → v.adicCompletion ℚ) i ∈ v.adicCompletionIntegers ℚ := by
    intro i; fin_cases i
    · exact hεinvmem
    · exact one_mem _
  have hℓe0 : ((ℓ : v.adicCompletion ℚ) ^ e) ≠ 0 :=
    pow_ne_zero _ (natCast_adicCompletion_ne_zero v hℓ.ne_zero)

  have hconjD : ∀ d : Fin 2 → v.adicCompletion ℚ,
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹] * Matrix.diagonal d *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ) ^ e] = Matrix.diagonal d := by
    intro d
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hℓe0, one_mul]

  have hmem : ∀ (d : Fin 2 → v.adicCompletion ℚ), (∀ i, d i ∈ v.adicCompletionIntegers ℚ) →
      ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        ψ y = (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Matrix.diagonal d * ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) →
        y ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
    intro d hd y hy
    have hc : ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * ψ y * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = Matrix.diagonal d := by
      rw [hy]; exact units_conj_conj h (Matrix.diagonal d)
    rw [mem_localBox_inf_iff hΛ₁.isOrder hΛ₂.isOrder]
    refine ⟨(hΛ₁v y).2 fun i j => ?_, (hΛ₂v y).2 fun i j => ?_⟩
    · rw [hc]
      exact diagonal_entries_mem _ d hd i j
    · rw [mul_assoc (Matrix.diagonal _) ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)),
        mul_assoc (Matrix.diagonal _) (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * _) (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)), hc, hconjD]
      exact diagonal_entries_mem _ d hd i j
  refine ⟨x, x', hmem _ hDmem x hψx, hmem _ hD'mem x' hψx', ?_, ?_, ?_⟩
  · apply ψ.injective
    rw [map_mul, hx, hx', RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Units.mul_inv, map_one]
  · apply ψ.injective
    rw [map_mul, hx, hx', RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Units.inv_mul, map_one]
  · intro φ hφ
    rw [hφ.nrd_eq_det ψ hψ1, hψx]
    rw [Matrix.det_units_conj, hD, Matrix.det_diagonal]
    simp

end Split

section Ramified

variable {a b : ℚ}

theorem exists_local_unit_ramified
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : ((2 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (ε : v.adicCompletion ℚ) (hε : Valued.v ε = 1) :
    ∃ x x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧ x' ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧
      x * x' = 1 ∧ x' * x = 1 ∧
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        IsCoord a b v φ → QuaternionAlgebra.nrd (φ x) = ε := by
  classical
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v).2 hqv
  have hε0 : ε ≠ 0 := fun h0 => by rw [h0, map_zero] at hε; exact zero_ne_one hε

  obtain ⟨m, s, hm, hms⟩ := exists_natCast_mul_sq_eq_of_valued_eq_one v hqv ε hε
  obtain ⟨γ, hγ⟩ := QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two hdef (m : ℚ)
    (Nat.cast_pos.2 hm)
  set x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ := γ ⊗ₜ[ℚ] s with hx
  have hnrd : ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
      IsCoord a b v φ → QuaternionAlgebra.nrd (φ x) = ε := fun φ hφ => by
    rw [hx, hφ.nrd_tmul, hγ, mul_comm, hms]
  obtain ⟨φ₀, hφ₀⟩ := exists_isCoord a b v
  have hx0 : x ≠ 0 := fun h0 => by
    have := hnrd φ₀ hφ₀
    rw [h0, map_zero, QuaternionAlgebra.nrd_zero] at this
    exact hε0 this.symm
  obtain ⟨xu, hxu⟩ := hdiv x hx0
  set x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ := ((xu⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) with hx'
  have h1 : x * x' = 1 := by rw [hx', ← hxu, Units.mul_inv]
  have h2 : x' * x = 1 := by rw [hx', ← hxu, Units.inv_mul]
  have hnrd' : QuaternionAlgebra.nrd (φ₀ x') = ε⁻¹ := by
    have := congrArg (fun t => QuaternionAlgebra.nrd (φ₀ t)) h2
    simp only [map_mul, nrd_mul', map_one, QuaternionAlgebra.nrd_one, hnrd φ₀ hφ₀] at this
    exact eq_inv_of_mul_eq_one_left this
  have hεmem : ε ∈ v.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hε.le
  have hεinvmem : ε⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hε, inv_one]

  have hmem : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      QuaternionAlgebra.nrd (φ₀ y) ∈ v.adicCompletionIntegers ℚ → y ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v := by
    intro y hy
    rw [mem_localBox_inf_iff hΛ₁.isOrder hΛ₂.isOrder]
    exact ⟨(QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
        hΛ₁ v hdiv φ₀ hφ₀ y).2 hy,
      (QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
        hΛ₂ v hdiv φ₀ hφ₀ y).2 hy⟩
  refine ⟨x, x', hmem x ?_, hmem x' ?_, h1, h2, hnrd⟩
  · rw [hnrd φ₀ hφ₀]; exact hεmem
  · rw [hnrd']; exact hεinvmem

end Ramified

section Assembly

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem exists_mem_finiteIdeleStabilizer_of_local (R : Submodule ℤ ℍ[ℚ, a, b])
    (hR : QuaternionAlgebra.IsOrder R)
    (x x' : (v : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
    (hx : ∀ v, x v ∈ Submodule.localBox R v) (hx' : ∀ v, x' v ∈ Submodule.localBox R v)
    (h1 : ∀ v, x v * x' v = 1) (h2 : ∀ v, x' v * x v = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = x v := by
  obtain ⟨y, hy⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq R hR.fg hR.spanTop x
    (Filter.Eventually.of_forall hx)
  obtain ⟨y', hy'⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq R hR.fg hR.spanTop x'
    (Filter.Eventually.of_forall hx')
  have hyy' : y * y' = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => ?_
    rw [map_mul, hy, hy', h1, map_one]
  have hy'y : y' * y = 1 := by
    refine Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v => ?_
    rw [map_mul, hy, hy', h2, map_one]
  set u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := ⟨y, y', hyy', hy'y⟩ with hu
  refine ⟨u, ?_, fun v => hy v⟩
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits R hR]
  intro v
  rw [Submodule.mem_localBoxUnits_iff]
  constructor
  · rw [Units.coe_map]
    change Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v y ∈ _
    rw [hy]; exact hx v
  · rw [Units.coe_map_inv]
    change Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v y' ∈ _
    rw [hy']; exact hx' v

end Assembly

section Main

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem main
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            ((u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))) = ε w := by
  classical
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, rfl, -⟩ := hR
  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ x x' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w ∧ x' ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w ∧
      x * x' = 1 ∧ x' * x = 1 ∧
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → QuaternionAlgebra.nrd (φ x) = ε w := by
    intro w
    by_cases hqw : ((2 : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact exists_local_unit_ramified hdef hΛ₁ hΛ₂ w hqw (ε w) (hε w)
    · exact exists_local_unit_split hdef hΛ₁ hΛ₂ w hqw (ε w) (hε w)
  choose x x' hx hx' h1 h2 hn using hloc
  obtain ⟨u, hu, hux⟩ := exists_mem_finiteIdeleStabilizer_of_local (Λ₁ ⊓ Λ₂) (hΛ₁.isOrder.inf hΛ₂.isOrder)
    x x' hx hx' h1 h2
  exact ⟨u, hu, fun w φ hφ => by rw [hux]; exact hn w φ hφ⟩

end Main

end LNCC2

end

open LNCC2 in
theorem solution
    {a b : ℚ} (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b 2)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            ((u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
              ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = ε w :=
  LNCC2.main hdef hR ε hε

end S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two (solution)
