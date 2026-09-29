-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1eba36dc-bb81-55a1-afbe-186ffdef3092

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
import Theorems.Thm_QuaternionAlgebra_exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne
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

namespace P2mNormalize

section Places

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span_natGenerator (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_natGenerator_self (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) =
      algebraMap (𝓞 ℚ) ℚ ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_natGenerator w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem natGenerator_injective {w w' : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator w = Rat.HeightOneSpectrum.natGenerator w') : w = w' := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

theorem valuation_natGenerator_of_ne (w w' : HeightOneSpectrum (𝓞 ℚ)) (h : w' ≠ w) :
    w.valuation ℚ ((Rat.HeightOneSpectrum.natGenerator w' : ℕ) : ℚ) = 1 := by
  refine valuation_natCast_eq_one_of_notMem w _ fun hmem => h ?_
  rw [natCast_mem_asIdeal_iff] at hmem
  have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w)
    (Rat.HeightOneSpectrum.prime_natGenerator w')).mp hmem
  exact (natGenerator_injective this).symm

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem not_mem_asIdeal_of_prime_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrq : r ≠ q) (hrw : (r : 𝓞 ℚ) ∈ w.asIdeal) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hqw
  rw [natCast_mem_asIdeal_iff] at hrw hqw
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hr).mp hrw
  have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp hqw
  exact hrq (h1.symm.trans h2)

end Places

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

section Coord

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

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

def coord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  Classical.choose (exists_isCoord a b w)

theorem isCoord_coord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) : IsCoord a b w (coord a b w) :=
  Classical.choose_spec (exists_isCoord a b w)

theorem isCoord_unique {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (hφ' : IsCoord a b w φ') (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    φ x = φ' x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z r => rw [hφ, hφ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem IsCoord.one_tmul {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (r : w.adicCompletion ℚ) :
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • 1 := by
  rw [hφ]
  congr 1

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

variable (a b)

def locNrd (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x))

variable {a b}

theorem locNrd_mul (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    locNrd a b w φ (x * y) = locNrd a b w φ x * locNrd a b w φ y := by
  simp only [locNrd, map_mul, nrd_mul']

theorem locNrd_one (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) :
    locNrd a b w φ 1 = 1 := by
  simp only [locNrd, map_one, QuaternionAlgebra.nrd_one]

theorem locNrd_units_inv (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) *
      locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
  rw [← locNrd_mul, Units.inv_mul, locNrd_one]

theorem locNrd_units_inv_eq (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))⁻¹ :=
  eq_inv_of_mul_eq_one_left (locNrd_units_inv w φ x)

theorem locNrd_units_ne_zero (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ≠ 0 := by
  intro h
  have := locNrd_units_inv w φ x
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem locNrd_eq_of_isCoord {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ φ' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (hφ' : IsCoord a b w φ') (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    locNrd a b w φ x = locNrd a b w φ' x := by
  simp only [locNrd, isCoord_unique hφ hφ']

theorem locNrd_diagonal {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : ℍ[ℚ, a, b]) :
    locNrd a b w φ (γ ⊗ₜ[ℚ] (1 : 𝔸f)) = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd γ) := by
  simp only [locNrd, Submodule.finiteAdeleEvalAt_tmul]
  rw [show ((1 : 𝔸f) w) = (1 : w.adicCompletion ℚ) from rfl, hφ, one_smul, QuaternionAlgebra.nrd_mk,
    QuaternionAlgebra.nrd]
  simp only [map_add, map_sub, map_mul, map_pow]

theorem locNrd_finiteIdeleDiagonal {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : (ℍ[ℚ, a, b])ˣ) :
    locNrd a b w φ ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
      = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b])) := by
  rw [Submodule.val_finiteIdeleDiagonal_apply, locNrd_diagonal hφ]

end Coord

section AlmostAll

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem eventually_algebraMap_mem_integers (r : ℚ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      algebraMap ℚ (w.adicCompletion ℚ) r ∈ w.adicCompletionIntegers ℚ :=
  (algebraMap ℚ 𝔸f r).2

theorem eventually_coords_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).re ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imI ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imJ ∈ w.adicCompletionIntegers ℚ ∧
        (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x)).imK ∈ w.adicCompletionIntegers ℚ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine Filter.Eventually.of_forall fun w φ hφ => ?_
    rw [map_zero, map_zero]
    exact ⟨zero_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  | tmul z s =>
    filter_upwards [s.2, eventually_algebraMap_mem_integers z.re, eventually_algebraMap_mem_integers z.imI,
      eventually_algebraMap_mem_integers z.imJ, eventually_algebraMap_mem_integers z.imK]
      with w hs h0 h1 h2 h3
    intro φ hφ
    rw [Submodule.finiteAdeleEvalAt_tmul, hφ]
    exact ⟨mul_mem hs h0, mul_mem hs h1, mul_mem hs h2, mul_mem hs h3⟩
  | add x y hx hy =>
    filter_upwards [hx, hy] with w hx hy
    intro φ hφ
    obtain ⟨h0, h1, h2, h3⟩ := hx φ hφ
    obtain ⟨k0, k1, k2, k3⟩ := hy φ hφ
    rw [map_add, map_add]
    exact ⟨add_mem h0 k0, add_mem h1 k1, add_mem h2 k2, add_mem h3 k3⟩

theorem eventually_locNrd_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → locNrd a b w φ x ∈ w.adicCompletionIntegers ℚ := by
  filter_upwards [eventually_coords_mem_integers x, eventually_algebraMap_mem_integers a,
    eventually_algebraMap_mem_integers b] with w hx ha hb
  intro φ hφ
  obtain ⟨h0, h1, h2, h3⟩ := hx φ hφ
  simp only [locNrd, QuaternionAlgebra.nrd]
  refine add_mem (sub_mem (sub_mem (pow_mem h0 2) (mul_mem ha (pow_mem h1 2))) (mul_mem hb (pow_mem h2 2)))
    (mul_mem (mul_mem ha hb) (pow_mem h3 2))

theorem eventually_valued_locNrd_eq_one (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) = 1 := by
  filter_upwards [eventually_locNrd_mem_integers (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f),
    eventually_locNrd_mem_integers ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)] with w hx hxi
  intro φ hφ
  have h1 : Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx φ hφ)
  have h2 : Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hxi φ hφ)
  have hprod : Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) *
      Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) = 1 := by
    rw [← map_mul, locNrd_units_inv, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (locNrd a b w φ ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) *
          Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := hprod.symm
    _ ≤ 1 * Valued.v (locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := mul_le_mul_of_nonneg_right h2 zero_le'
    _ = _ := one_mul _

end AlmostAll

section Rational

theorem exists_rat_valued_eq (n : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hn0 : ∀ w, n w ≠ 0) (hn : ∀ᶠ w in Filter.cofinite, Valued.v (n w) = 1) :
    ∃ t : ℚ, 0 < t ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) t) = Valued.v (n w) := by
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 ℚ) | ¬ Valued.v (n w) = 1}.Finite := Filter.eventually_cofinite.1 hn
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ Valued.v (n w) ≠ 1 := fun w => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  let k : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun w => WithZero.log (Valued.v (n w))
  have hk : ∀ w, WithZero.exp (k w) = Valued.v (n w) := fun w =>
    WithZero.exp_log ((Valuation.ne_zero_iff _).2 (hn0 w))
  let p : HeightOneSpectrum (𝓞 ℚ) → ℚ := fun w => ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ)
  have hp_pos : ∀ w, 0 < p w := fun w => by
    show (0 : ℚ) < ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ)
    exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).pos
  refine ⟨∏ w ∈ S, p w ^ (-(k w)), Finset.prod_pos fun w _ => zpow_pos (hp_pos w) _, fun w => ?_⟩
  rw [valued_algebraMap, map_prod]
  simp only [map_zpow₀]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single w]
    · rw [show p w = ((Rat.HeightOneSpectrum.natGenerator w : ℕ) : ℚ) from rfl, valuation_natGenerator_self,
        ← WithZero.exp_zsmul, smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, hk]
    · intro w' _ hw'
      rw [show p w' = ((Rat.HeightOneSpectrum.natGenerator w' : ℕ) : ℚ) from rfl,
        valuation_natGenerator_of_ne w w' hw', one_zpow]
    · intro h; exact absurd hw h
  · rw [Finset.prod_eq_one]
    · have := (hmemS w).not.1 hw
      push Not at this
      exact this.symm
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [show p w' = ((Rat.HeightOneSpectrum.natGenerator w' : ℕ) : ℚ) from rfl,
        valuation_natGenerator_of_ne w w' hne, one_zpow]

end Rational

section Frame

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem exists_nrd_eq_of_pos' {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    (t : ℚ) (ht : 0 < t) : ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = t := by
  by_cases hq2 : q = 2
  · subst hq2
    exact QuaternionAlgebra.exists_nrd_eq_of_pos_of_isDefiniteRamifiedExactlyAt_two hdef t ht
  · exact QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hq2 hdef t ht

theorem exists_mem_finiteIdeleStabilizer_forall_nrd_eq' {q : ℕ} [Fact q.Prime]
    (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → locNrd a b w φ ((u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = ε w := by
  by_cases hq2 : q = 2
  · subst hq2
    obtain ⟨u, hu, h⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_isDefiniteRamifiedExactlyAt_two
        hdef hR ε hε
    exact ⟨u, hu, fun w φ hφ => h w φ hφ⟩
  · obtain ⟨u, hu, h⟩ :=
      QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq hq2 hdef hR ε hε
    exact ⟨u, hu, fun w φ hφ => h w φ hφ⟩

theorem exists_frame {q : ℕ} [Fact q.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {O : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hO : QuaternionAlgebra.IsEichlerOrder O N)
    (r : ℕ) [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∃ (β : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer O ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ u₁ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ, u₁ ∈ Submodule.finiteIdeleStabilizer O ∧
        locNrd a b w (coord a b w) (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          locNrd a b w (coord a b w) ((u₁⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∧
        locNrd a b w (coord a b w) ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          locNrd a b w (coord a b w) (u₁ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * g * u := by
  classical
  have hqP : q.Prime := Fact.out
  have hrP : r.Prime := Fact.out

  let n : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ := fun w =>
    locNrd a b w (coord a b w) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
  have hn0 : ∀ w, n w ≠ 0 := fun w => locNrd_units_ne_zero w _ x
  have hn1 : ∀ᶠ w in Filter.cofinite, Valued.v (n w) = 1 := by
    filter_upwards [eventually_valued_locNrd_eq_one x] with w hw
    exact hw _ (isCoord_coord a b w)
  obtain ⟨t, ht, hvt⟩ := exists_rat_valued_eq n hn0 hn1
  have ht0 : t ≠ 0 := ht.ne'
  have htw : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) t ≠ 0 := fun w => by
    simpa using (algebraMap ℚ (w.adicCompletion ℚ)).injective.ne ht0

  obtain ⟨γ₀, hγ₀⟩ := exists_nrd_eq_of_pos' hdef t ht
  have hγ₀inv : γ₀ * (t⁻¹ • star γ₀) = 1 := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, hγ₀]
    ext <;> simp [ht0]
  have hγ₀inv' : (t⁻¹ • star γ₀) * γ₀ = 1 := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, hγ₀]
    ext <;> simp [ht0]
  let γ₀u : (ℍ[ℚ, a, b])ˣ := ⟨γ₀, t⁻¹ • star γ₀, hγ₀inv, hγ₀inv'⟩

  let ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ := fun w =>
    (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ * n w
  have hε : ∀ w, Valued.v (ε w) = 1 := fun w => by
    simp only [ε, map_mul, map_inv₀, hvt w]
    exact inv_mul_cancel₀ ((Valuation.ne_zero_iff _).2 (hn0 w))
  obtain ⟨u₀, hu₀, hu₀n⟩ := exists_mem_finiteIdeleStabilizer_forall_nrd_eq' hdef hO ε hε

  set y : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u)⁻¹ * x * u₀⁻¹ with hy_def
  have hy1 : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ → locNrd a b w φ (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    intro w φ hφ
    have hdiag : locNrd a b w φ ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = algebraMap ℚ (w.adicCompletion ℚ) t := by
      rw [locNrd_finiteIdeleDiagonal hφ]
      change algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd γ₀) = _
      rw [hγ₀]
    have hdiag_inv : locNrd a b w φ (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u)⁻¹ :
        (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ := by
      rw [locNrd_units_inv_eq, hdiag]
    have hu₀w : locNrd a b w φ (u₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = ε w := hu₀n w φ hφ
    have hu₀w_inv : locNrd a b w φ ((u₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = (ε w)⁻¹ := by
      rw [locNrd_units_inv_eq, hu₀w]
    have hxw : locNrd a b w φ (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = n w :=
      locNrd_eq_of_isCoord hφ (isCoord_coord a b w) _
    rw [hy_def, Units.val_mul, Units.val_mul, locNrd_mul, locNrd_mul, hdiag_inv, hxw, hu₀w_inv]
    simp only [ε]
    have key : (algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ *
        (n w * ((algebraMap ℚ (w.adicCompletion ℚ) t)⁻¹ * n w)⁻¹) = 1 := by
      rw [mul_inv, inv_inv, mul_comm (algebraMap ℚ (w.adicCompletion ℚ) t) (n w)⁻¹, ← mul_assoc (n w),
        mul_inv_cancel₀ (hn0 w), one_mul, inv_mul_cancel₀ (htw w)]
    rwa [mul_assoc]

  have hsplit : ∃ z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, z ≠ 0 ∧ ¬ IsUnit z := by
    have hqv : (q : 𝓞 ℚ) ∉ v.asIdeal := not_mem_asIdeal_of_prime_of_ne v hrP hqP hrq hv
    have h := (hdef.2.2 v).not.2 hqv
    push Not at h
    exact h
  obtain ⟨β₁, g, u₁, hβ₁, hu₁, hg, hyeq⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one
      hdef.neg_left hdef.neg_right hO.isOrder v hsplit y (fun w hw φ hφ => hy1 w φ hφ)

  refine ⟨γ₀u * β₁, g, u₁ * u₀, Subgroup.mul_mem _ hu₁ hu₀, hg, fun w => ⟨u₁, hu₁, ?_, ?_⟩, ?_⟩
  ·
    have hg' : g = (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β₁)⁻¹ * y * u₁⁻¹ := by
      rw [hyeq]; group
    rw [hg', Units.val_mul, Units.val_mul, locNrd_mul, locNrd_mul, locNrd_units_inv_eq,
      locNrd_finiteIdeleDiagonal (isCoord_coord a b w), hβ₁, map_one, inv_one, one_mul,
      hy1 w _ (isCoord_coord a b w), one_mul]
  · have hg' : g⁻¹ = u₁ * y⁻¹ * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β₁ := by
      rw [hyeq]; group
    have hyinv : locNrd a b w (coord a b w) ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
      rw [locNrd_units_inv_eq, hy1 w _ (isCoord_coord a b w), inv_one]
    rw [hg', Units.val_mul, Units.val_mul, locNrd_mul, locNrd_mul, hyinv, mul_one,
      locNrd_finiteIdeleDiagonal (isCoord_coord a b w), hβ₁, map_one, mul_one]
  · have hx : x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ₀u * y * u₀ := by
      rw [hy_def]; group
    rw [hx, hyeq, map_mul]
    group

end Frame

end P2mNormalize

end

open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N]
    {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q')
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ (γ : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer R ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      x = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g * u := by
  obtain ⟨γ, g, u, hu, hg, -, hx⟩ := P2mNormalize.exists_frame hdef hR r hrq' v hv x
  exact ⟨γ, g, u, hu, hg, hx⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne (solution)
