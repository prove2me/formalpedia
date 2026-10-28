-- Prove2me | solution 1 for OrbNetEqui.Equivariance.evNorm_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:06:37.685591+00:00
-- url     : https://prove2.me/submissions/3a6a1347-a880-4983-8fe3-3a64afe05cdc

import Init
import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic


section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
universe u

theorem unitary_sum_normSq {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix.unitaryGroup ι ℂ) (x : ι → ℂ) :
    ∑ i, Complex.normSq (((A : Matrix ι ι ℂ) *ᵥ x) i) = ∑ i, Complex.normSq (x i) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  change star ((A : Matrix ι ι ℂ) *ᵥ x) ⬝ᵥ ((A : Matrix ι ι ℂ) *ᵥ x) = star x ⬝ᵥ x
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose,Matrix.UnitaryGroup.star_mul_self,Matrix.one_mulVec]

theorem regNorm_unitary {m : ℕ} (A : Matrix.unitaryGroup (Fin m) ℂ)
    (ε : ℝ) (x : Fin m → ℂ) : regNorm ε ((A : Matrix (Fin m) (Fin m) ℂ) *ᵥ x) = regNorm ε x := by
  simp only [regNorm,Finset.sum_add_distrib,unitary_sum_normSq]

theorem evNorm_general {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) := by
  constructor
  · funext L c
    simp only [evNormBar,featAct,regNorm_unitary]
  · funext L c M
    change ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ x L c) M /
      ((regNorm ε ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ x L c) + 1 / β L c + ε : ℝ) : ℂ) =
      ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ
        (fun m => x L c m / ((regNorm ε (x L c) + 1 / β L c + ε : ℝ) : ℂ))) M
    rw [regNorm_unitary]
    simp only [Matrix.mulVec,dotProduct,← mul_div_assoc,← Finset.sum_div]

end Queelius.UniteEquivariance

namespace OrbNetEqui.Equivariance
open Matrix

theorem evNorm_equivariant {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (hβ : ∀ L c, 0 < β L c) (hε : 0 < ε)
    (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) :=
  Queelius.UniteEquivariance.evNorm_general U μ σ β ε k x

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance
universe u v w

def pairVector {ι : Type u} {κ : Type v} (x : ι → ℂ) (y : κ → ℂ) : ι × κ → ℂ :=
  fun ij => x ij.1 * y ij.2

theorem kronecker_pairVector {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (x : ι → ℂ) (y : κ → ℂ) :
    (Matrix.kroneckerMap (· * ·) A B) *ᵥ pairVector x y = pairVector (A *ᵥ x) (B *ᵥ y) := by
  funext ij
  simp only [Matrix.mulVec,dotProduct,pairVector,Matrix.kroneckerMap_apply,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def couple {ι : Type u} {κ : Type v} {τ : Type w} [Fintype ι] [Fintype κ]
    (C : Matrix τ (ι × κ) ℂ) (x : ι → ℂ) (y : κ → ℂ) : τ → ℂ := C *ᵥ pairVector x y

theorem couple_intertwines {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (D : Matrix τ τ ℂ)
    (C : Matrix τ (ι × κ) ℂ) (hC : C * Matrix.kroneckerMap (· * ·) A B = D * C)
    (x : ι → ℂ) (y : κ → ℂ) :
    couple C (A *ᵥ x) (B *ᵥ y) = D *ᵥ couple C x y := by
  unfold couple
  rw [← kronecker_pairVector,Matrix.mulVec_mulVec,hC,Matrix.mulVec_mulVec]

theorem couple_apply {ι : Type u} {κ : Type v} {τ : Type w} [Fintype ι] [Fintype κ]
    (C : Matrix τ (ι × κ) ℂ) (x : ι → ℂ) (y : κ → ℂ) (i : τ) :
    couple C x y i = ∑ a, ∑ b, x a * y b * C i (a,b) := by
  simp only [couple,Matrix.mulVec,dotProduct,pairVector,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

def coupledFeatures {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (h g : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c => ∑ L₁, ∑ L₂, couple (C c L₁ L₂ L) (h L₁ c) (g L₂ c)

theorem coupledFeatures_equivariant {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (k : K) (hC : ∀ c L₁ L₂ L, C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
      (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
      (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * C c L₁ L₂ L)
    (h g : Feature Λ dim nmax) :
    coupledFeatures C (featAct U k h) (featAct U k g) = featAct U k (coupledFeatures C h g) := by
  funext L c
  dsimp [coupledFeatures,featAct]
  simp only [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro L₁ hL₁
  apply Finset.sum_congr rfl
  intro L₂ hL₂
  exact couple_intertwines _ _ _ _ (hC c L₁ L₂ L) _ _

end Queelius.UniteEquivariance

end

section
open Matrix OrbNetEqui.Equivariance

theorem solution {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (hβ : ∀ L c, 0 < β L c) (hε : 0 < ε)
    (k : K) (x : Feature Λ dim nmax) :
    evNormBar μ σ ε (featAct U k x) = evNormBar μ σ ε x ∧
      evNormHat β ε (featAct U k x) = featAct U k (evNormHat β ε x) :=
  evNorm_equivariant U μ σ β ε hβ hε k x

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

def gatedFeature {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (mlp : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ))
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) : Feature Λ dim nmax :=
  fun L c M => (mlp (evNormBar μ σ ε h) L c : ℂ) * evNormHat β ε h L c M

theorem featAct_add {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (k : K)
    (h g : Feature Λ dim nmax) : featAct U k (h+g) = featAct U k h + featAct U k g := by
  funext L c M
  exact congrFun (Matrix.mulVec_add _ (h L c) (g L c)) M

theorem gatedFeature_equivariant {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ) (k : K)
    (mlp : (Λ → Fin nmax → ℝ) → (Λ → Fin nmax → ℝ))
    (μ σ β : Λ → Fin nmax → ℝ) (ε : ℝ) (h : Feature Λ dim nmax) :
    gatedFeature mlp μ σ β ε (featAct U k h) = featAct U k (gatedFeature mlp μ σ β ε h) := by
  have hb := (evNorm_general U μ σ β ε k h).1
  have hh := (evNorm_general U μ σ β ε k h).2
  unfold gatedFeature
  rw [hb,hh]
  funext L c M
  change (mlp (evNormBar μ σ ε h) L c : ℂ) *
      ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ evNormHat β ε h L c) M =
    ((U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ
      (fun m => (mlp (evNormBar μ σ ε h) L c : ℂ) * evNormHat β ε h L c m)) M
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem coupledFeatures_expansion {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (C : Fin nmax → (L₁ L₂ L : Λ) → Matrix (Fin (dim L)) (Fin (dim L₁) × Fin (dim L₂)) ℂ)
    (h g : Feature Λ dim nmax) :
    coupledFeatures C h g = fun L c M => ∑ L₁, ∑ L₂, ∑ M₁, ∑ M₂,
      h L₁ c M₁ * g L₂ c M₂ * C c L₁ L₂ L M (M₁,M₂) := by
  funext L c M
  simp only [coupledFeatures,Finset.sum_apply,couple_apply]

theorem pointwise_factorization {Λ : Type*} [Fintype Λ] {dim : Λ → ℕ} {nmax : ℕ}
    (P : PointwiseParams Λ dim nmax) (ε : ℝ) (h g : Feature Λ dim nmax) :
    pointwise P ε h g = h + gatedFeature P.mlp₂ P.μq P.σq P.βq ε
      (g + coupledFeatures P.C (gatedFeature P.mlp₁ P.μh P.σh P.βh ε h) g) := by
  rw [coupledFeatures_expansion]
  rfl

theorem pointwise_general {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (P : PointwiseParams Λ dim nmax) (ε : ℝ) (k : K)
    (hC : ∀ c L₁ L₂ L, P.C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
      (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
      (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
      (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * P.C c L₁ L₂ L)
    (h g : Feature Λ dim nmax) :
    pointwise P ε (featAct U k h) (featAct U k g) = featAct U k (pointwise P ε h g) := by
  rw [pointwise_factorization,pointwise_factorization,gatedFeature_equivariant,
    coupledFeatures_equivariant U P.C k hC]
  rw [← featAct_add,gatedFeature_equivariant,← featAct_add]

end Queelius.UniteEquivariance

namespace OrbNetEqui.Equivariance
open Matrix

theorem pointwise_equivariant {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (P : PointwiseParams Λ dim nmax) (ε : ℝ)
    (hβ : ∀ L c, 0 < P.βh L c ∧ 0 < P.βq L c) (hε : 0 < ε) (k : K)
    (hC : ∀ (c : Fin nmax) (L₁ L₂ L : Λ),
      P.C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
          (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
          (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * P.C c L₁ L₂ L)
    (h g' : Feature Λ dim nmax) :
    pointwise P ε (featAct U k h) (featAct U k g') = featAct U k (pointwise P ε h g') :=
  Queelius.UniteEquivariance.pointwise_general U P ε k hC h g'

end OrbNetEqui.Equivariance

end

section
noncomputable section
namespace Queelius.UniteEquivariance
open Matrix Finset OrbNetEqui.Equivariance

theorem regNorm_nonnegative {m : ℕ} (ε : ℝ) (x : Fin m → ℂ) : 0 ≤ regNorm ε x := by
  have hsum : 0 ≤ ∑ M, Complex.normSq (x M) := Finset.sum_nonneg (fun M hM => Complex.normSq_nonneg _)
  unfold regNorm
  apply sub_nonneg.mpr
  calc
    ε ≤ |ε| := le_abs_self ε
    _ = Real.sqrt (ε^2) := (Real.sqrt_sq_eq_abs ε).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

theorem direction_denominator_positive {m : ℕ} (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (x : Fin m → ℂ) : 0 < regNorm ε x + 1/β + ε := by
  have hn := regNorm_nonnegative ε x
  have hi := one_div_pos.mpr hβ
  linarith

theorem regNorm_zero {m : ℕ} (ε : ℝ) (hε : 0 ≤ ε) :
    regNorm ε (fun _ : Fin m => (0 : ℂ)) = 0 := by
  simp [regNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg hε]

end Queelius.UniteEquivariance

namespace Queelius.UniteEquivariance.Controls
open Matrix Finset OrbNetEqui.Equivariance

def quarterTurn : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0,-1;1,0], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Fin.sum_univ_two]⟩

def sampleVector : Fin 2 → ℂ := ![3,4]

theorem quarterTurn_sample : (quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector = ![-4,3] := by
  ext i
  fin_cases i <;> norm_num [quarterTurn,sampleVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem regularized_sample : regNorm 12 sampleVector = 1 := by
  norm_num [regNorm,sampleVector,Fin.sum_univ_two,Complex.normSq]

theorem regularized_rotated : regNorm 12 ((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) = 1 := by
  rw [regNorm_unitary,regularized_sample]

def standardRep (_ : Unit) : Matrix.unitaryGroup (Fin 2) ℂ →* Matrix.unitaryGroup (Fin 2) ℂ :=
  MonoidHom.id _

def sampleFeature : Feature Unit (fun _ => 2) 1 := fun _ _ => sampleVector

theorem sample_direction : evNormHat (fun (_ : Unit) (_ : Fin 1) => 1) 12 sampleFeature () 0 =
    fun m => sampleVector m / 14 := by
  ext m
  norm_num [evNormHat,sampleFeature,regularized_sample]

theorem sample_bar : evNormBar (fun (_ : Unit) (_ : Fin 1) => 0) (fun _ _ => 1)
    12 sampleFeature () 0 = 1 := by
  simp [evNormBar,sampleFeature,regularized_sample]

theorem rotated_direction :
    evNormHat (fun (_ : Unit) (_ : Fin 1) => 1) 12 (featAct standardRep quarterTurn sampleFeature) () 0 =
      fun m => (![-4,3] : Fin 2 → ℂ) m / 14 := by
  change (fun m => (((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) m) /
    ((regNorm 12 ((quarterTurn : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ sampleVector) + 1/(1 : ℝ) + 12 : ℝ) : ℂ)) = _
  rw [regularized_rotated,quarterTurn_sample]
  norm_num

end Queelius.UniteEquivariance.Controls

end

section
noncomputable section
namespace Queelius.UniteEquivariance.Controls
open Matrix Finset OrbNetEqui.Equivariance

def phaseUnitary : Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨!![Complex.I], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.star_eq_conjTranspose,Matrix.mul_apply,Fin.sum_univ_one]⟩

def scalarCoupling : Matrix (Fin 1) (Fin 1 × Fin 1) ℂ := fun _ _ => 1

theorem phase_intertwines :
    scalarCoupling * Matrix.kroneckerMap (· * ·)
      (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) (phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) =
    (-1 : Matrix (Fin 1) (Fin 1) ℂ) * scalarCoupling := by
  ext i j
  fin_cases i
  rcases j with ⟨j,k⟩
  fin_cases j
  fin_cases k
  norm_num [scalarCoupling,phaseUnitary,Matrix.mul_apply,Matrix.kroneckerMap,Fintype.sum_prod_type,Fin.sum_univ_one]

theorem phase_coupling_nonzero :
    couple scalarCoupling (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 0 = 6 ∧
    couple scalarCoupling
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (2 : ℂ))
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (3 : ℂ)) 0 = -6 := by
  constructor
  · norm_num [couple,scalarCoupling,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_one]
  · rw [couple_intertwines _ _ _ _ phase_intertwines]
    norm_num [couple,scalarCoupling,pairVector,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_one]

theorem wrong_output_phase_fails :
    couple scalarCoupling
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (2 : ℂ))
      ((phaseUnitary : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ fun _ => (3 : ℂ)) ≠
    (1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ couple scalarCoupling (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) := by
  intro h
  have hh := congrFun h 0
  rw [Matrix.one_mulVec,phase_coupling_nonzero.1,phase_coupling_nonzero.2] at hh
  norm_num at hh

end Queelius.UniteEquivariance.Controls

end
