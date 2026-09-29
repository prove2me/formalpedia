-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3ab9ee36-1e95-52f6-a54e-ca1177c73e9c

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit
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

namespace LNSPLIT

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

theorem natCast_adicCompletion_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (w.adicCompletion ℚ)) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

end Places

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

section Chart

variable {a b : ℚ}

theorem exists_matrixChart_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0)
    (w : HeightOneSpectrum (𝓞 ℚ))
    (hns : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∃ ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ),
      ∀ r : w.adicCompletion ℚ,
        ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isCoord a b w
  push Not at hns
  obtain ⟨y, hy0, hyu⟩ := hns

  set z := φ y with hz
  have hz0 : z ≠ 0 := fun h => hy0 (by
    apply φ.injective
    rw [← hz, h, map_zero])
  have hzu : ¬ IsUnit z := fun h => hyu (by
    have := h.map φ.symm
    rwa [hz, RingEquiv.symm_apply_apply] at this)
  haveI : CharZero (w.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (w.adicCompletion ℚ)).injective
  haveI : NeZero (2 : w.adicCompletion ℚ) := ⟨two_ne_zero⟩
  have ha' : algebraMap ℚ (w.adicCompletion ℚ) a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : algebraMap ℚ (w.adicCompletion ℚ) b ≠ 0 := (map_ne_zero _).2 hb
  obtain ⟨θ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit ha' hb' z hz0 hzu
  obtain ⟨ψ, hψ1, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl θ
  exact ⟨ψ, hψ1⟩

end Chart

section Boxes

variable {a b : ℚ}

theorem mem_localBox_inf_iff {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (h₁ : QuaternionAlgebra.IsOrder Λ₁) (h₂ : QuaternionAlgebra.IsOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ↔ x ∈ Submodule.localBox Λ₁ v ∧ x ∈ Submodule.localBox Λ₂ v := by
  rw [Submodule.localBox_inf Λ₁ Λ₂ h₁.fg h₁.spanTop h₂.fg h₂.spanTop v, AddSubgroup.mem_inf]

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  refine AddSubgroup.subset_closure ⟨1, h1, 1, one_mem _, ?_⟩
  rfl

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

theorem exists_local_unit_split
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hns : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    (ε : v.adicCompletion ℚ) (hε : Valued.v ε = 1) :
    ∃ x x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧ x' ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧
      x * x' = 1 ∧ x' * x = 1 ∧
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        IsCoord a b v φ → QuaternionAlgebra.nrd (φ x) = ε := by
  classical

  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ₁
  obtain ⟨ψ, hψ1⟩ := exists_matrixChart_of_not_forall_isUnit ha hb v hns

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

theorem exists_local_unit
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (ε : v.adicCompletion ℚ) (hε : Valued.v ε = 1) :
    ∃ x x' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧ x' ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ∧
      x * x' = 1 ∧ x' * x = 1 ∧
      ((¬ ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) →
        ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
            ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
          IsCoord a b v φ → QuaternionAlgebra.nrd (φ x) = ε) := by
  by_cases hns : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y
  · refine ⟨1, 1, ?_, ?_, one_mul _, one_mul _, fun h => absurd hns h⟩
    · rw [mem_localBox_inf_iff hΛ₁.isOrder hΛ₂.isOrder]
      exact ⟨one_mem_localBox hΛ₁.isOrder.one_mem v, one_mem_localBox hΛ₂.isOrder.one_mem v⟩
    · rw [mem_localBox_inf_iff hΛ₁.isOrder hΛ₂.isOrder]
      exact ⟨one_mem_localBox hΛ₁.isOrder.one_mem v, one_mem_localBox hΛ₂.isOrder.one_mem v⟩
  · obtain ⟨x, x', hx, hx', h1, h2, hn⟩ := exists_local_unit_split hΛ₁ hΛ₂ v hns ε hε
    exact ⟨x, x', hx, hx', h1, h2, fun _ => hn⟩

end Split

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
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        (¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x) →
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            ((u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))) = ε w := by
  classical
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, rfl, -⟩ := hR
  have hloc := fun w : HeightOneSpectrum (𝓞 ℚ) => exists_local_unit hΛ₁ hΛ₂ w (ε w) (hε w)
  choose x x' hx hx' h1 h2 hn using hloc
  obtain ⟨u, hu, hux⟩ := exists_mem_finiteIdeleStabilizer_of_local (Λ₁ ⊓ Λ₂) (hΛ₁.isOrder.inf hΛ₂.isOrder)
    x x' hx hx' h1 h2
  exact ⟨u, hu, fun w hns φ hφ => by rw [hux]; exact hn w hns φ hφ⟩

end Main

end LNSPLIT

end

open LNSPLIT in
theorem solution
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ)
    (hε : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (ε w) = 1) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R,
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        (¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x) →
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
  LNSPLIT.main hR ε hε

end S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit (solution)
