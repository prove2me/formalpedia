-- Prove2me | solution 1 for PathFindingLP.WeightFunction.step_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T00:15:52.623748+00:00
-- url     : https://prove2.me/submissions/aa497d98-b304-41a7-b5a5-9b3ba7dcbbc5

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
import Definitions.Def_PathFindingLP_WeightFunction_IsWeightFunction

set_option autoImplicit false

open Matrix

/-- `N(e) = Aᵀ diag(e) A`. -/
noncomputable def scN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * diagonal e * A

/-- `Q(e) = A N(e)⁻¹ Aᵀ`. -/
noncomputable def scQm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  A * (scN A e)⁻¹ * Aᵀ

/-- Leverage-type scores `τ_i(e) = e_i Q_ii(e)`. -/
noncomputable def scT {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) : Fin m → ℝ :=
  fun i => e i * scQm A e i i

section Calc

open scoped Norms.Operator

/-- `e ↦ N(e)` as a linear map. -/
noncomputable def scNlin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun e := Aᵀ * diagonal e * A
  map_add' x y := by
    have h : diagonal (x + y) = diagonal x + diagonal y := (diagonal_add x y).symm
    rw [h, Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    have h : diagonal (c • x) = c • diagonal x := by
      ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
    rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- `X ↦ (A X Aᵀ)_{ii}` as a linear map. -/
noncomputable def scEnt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun X := (A * X * Aᵀ) i i
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c X := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

lemma scT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    scT A = fun e i => e i * scEnt A i (Ring.inverse (scNlin A e)) := by
  funext e i
  simp only [scT, scQm, scN, scEnt, scNlin, LinearMap.coe_mk, AddHom.coe_mk,
    nonsing_inv_eq_ringInverse]

lemma scT_hasFDerivAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e0 : Fin m → ℝ)
    (hu : IsUnit (scN A e0)) :
    ∃ T' : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ), HasFDerivAt (scT A) T' e0 ∧
      ∀ k i, T' k i = k i * scQm A e0 i i
        - e0 i * ∑ j, k j * scQm A e0 i j * scQm A e0 j i := by
  obtain ⟨u, hu⟩ := hu
  let NL : (Fin m → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ := LinearMap.toContinuousLinearMap (scNlin A)
  have hNe : NL e0 = (u : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hu]; rfl
  have hinv : HasFDerivAt (fun e => Ring.inverse (NL e))
      ((-ContinuousLinearMap.mulLeftRight ℝ _ ↑u⁻¹ ↑u⁻¹).comp NL) e0 := by
    have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [← hNe] at h1
    exact h1.comp e0 NL.hasFDerivAt
  have hcoord : ∀ i : Fin m, HasFDerivAt (fun e : Fin m → ℝ => e i)
      (ContinuousLinearMap.proj i) e0 := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasFDerivAt (x := e0)
  have hcomp : ∀ i : Fin m, HasFDerivAt (fun e => e i * scEnt A i (Ring.inverse (NL e)))
      (e0 i • ((LinearMap.toContinuousLinearMap (scEnt A i)).comp
          ((-ContinuousLinearMap.mulLeftRight ℝ _ ↑u⁻¹ ↑u⁻¹).comp NL))
        + (scEnt A i (Ring.inverse (NL e0))) • ContinuousLinearMap.proj i) e0 := by
    intro i
    have h2 : HasFDerivAt (fun e => scEnt A i (Ring.inverse (NL e)))
        ((LinearMap.toContinuousLinearMap (scEnt A i)).comp
          ((-ContinuousLinearMap.mulLeftRight ℝ _ ↑u⁻¹ ↑u⁻¹).comp NL)) e0 :=
      (LinearMap.toContinuousLinearMap (scEnt A i)).hasFDerivAt.comp e0 hinv
    exact (hcoord i).mul h2
  refine ⟨ContinuousLinearMap.pi fun i =>
      e0 i • ((LinearMap.toContinuousLinearMap (scEnt A i)).comp
          ((-ContinuousLinearMap.mulLeftRight ℝ _ ↑u⁻¹ ↑u⁻¹).comp NL))
        + (scEnt A i (Ring.inverse (NL e0))) • ContinuousLinearMap.proj i, ?_, ?_⟩
  · rw [scT_eq]
    exact hasFDerivAt_pi.mpr hcomp
  · intro k i
    have hR : Ring.inverse (NL e0) = (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
      rw [hNe, Ring.inverse_unit]
    have hX : (scN A e0)⁻¹ = (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
      rw [nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
    have hQ : scQm A e0 = A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ := by rw [scQm, hX]
    have hent : ∀ Y, scEnt A i Y = (A * Y * Aᵀ) i i := fun Y => rfl
    have hNk : NL k = Aᵀ * diagonal k * A := rfl
    change e0 i * scEnt A i (-((↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * NL k *
        (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ))) + scEnt A i (Ring.inverse (NL e0)) * k i = _
    rw [hR, hQ, map_neg, hent, hent, hNk]
    have hmat : A * ((↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (Aᵀ * diagonal k * A) *
          (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * Aᵀ
        = (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) * diagonal k *
          (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hmat, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    have : ∑ j, (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) i j * k j
          * (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) j i
        = ∑ j, k j * (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) i j
          * (A * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℝ) * Aᵀ) j i := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this]
    ring

end Calc

/-- `e_i = w_i^α / s_i²`. -/
noncomputable def scE {m : ℕ} (α : ℝ) (s w : Fin m → ℝ) : Fin m → ℝ :=
  fun i => w i ^ α * ((s i)⁻¹) ^ 2

/-- `Φ(s, w) = w − τ(E(s,w)) − β`. -/
noncomputable def scPhi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β : ℝ)
    (p : (Fin m → ℝ) × (Fin m → ℝ)) : Fin m → ℝ :=
  p.2 - scT A (scE α p.1 p.2) - fun _ => β

section Calc2

open scoped Norms.Operator

lemma scT_contDiffAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e0 : Fin m → ℝ)
    (hu : IsUnit (scN A e0)) : ContDiffAt ℝ 1 (scT A) e0 := by
  obtain ⟨u, hu⟩ := hu
  let NL : (Fin m → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap (scNlin A)
  have hNe : NL e0 = (u : Matrix (Fin n) (Fin n) ℝ) := by rw [hu]; rfl
  have hinv : ContDiffAt ℝ 1 (fun e => Ring.inverse (NL e)) e0 := by
    have h1 := contDiffAt_ringInverse ℝ (n := 1) u
    rw [← hNe] at h1
    exact h1.comp e0 NL.contDiff.contDiffAt
  have hc : ∀ i : Fin m, ContDiffAt ℝ 1 (fun e => e i * scEnt A i (Ring.inverse (NL e))) e0 := by
    intro i
    have h2 : ContDiffAt ℝ 1 (fun e => scEnt A i (Ring.inverse (NL e))) e0 :=
      (LinearMap.toContinuousLinearMap (scEnt A i)).contDiff.contDiffAt.comp e0 hinv
    have h3 : ContDiffAt ℝ 1 (fun e : Fin m → ℝ => e i) e0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).contDiff.contDiffAt
    exact h3.mul h2
  rw [scT_eq]
  exact contDiffAt_pi.mpr hc

end Calc2

lemma scE_coord {m : ℕ} (α : ℝ) (s w : Fin m → ℝ) (hs : ∀ i, s i ≠ 0) (hw : ∀ i, 0 < w i)
    (i : Fin m) :
    ∃ D : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ,
      HasFDerivAt (fun p : (Fin m → ℝ) × (Fin m → ℝ) => scE α p.1 p.2 i) D (s, w) ∧
      ∀ a b, D (a, b) = scE α s w i * (α * b i / w i - 2 * a i / s i) := by
  let Ls : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ _ _)
  let Lw : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ _ _)
  have hLs : HasFDerivAt (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.1 i) Ls (s, w) := Ls.hasFDerivAt
  have hLw : HasFDerivAt (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.2 i) Lw (s, w) := Lw.hasFDerivAt
  have h1 := hLw.rpow_const (p := α) (Or.inl (hw i).ne')
  have h2 := ((hasFDerivAt_inv (𝕜 := ℝ) (hs i)).comp (s, w) hLs).pow 2
  refine ⟨_, h1.mul h2, fun a b => ?_⟩
  have hwi := (hw i).ne'
  have hsi := hs i
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Ls, Lw, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply, scE]
  rw [Real.rpow_sub_one hwi]
  field_simp
  have hss : s i * (s i)⁻¹ = 1 := mul_inv_cancel₀ hsi
  linear_combination (-(w i ^ α * a i * w i * 2)) * hss

lemma scE_hasFDerivAt {m : ℕ} (α : ℝ) (s w : Fin m → ℝ) (hs : ∀ i, s i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    ∃ E' : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ),
      HasFDerivAt (fun p : (Fin m → ℝ) × (Fin m → ℝ) => scE α p.1 p.2) E' (s, w) ∧
      ∀ a b i, E' (a, b) i = scE α s w i * (α * b i / w i - 2 * a i / s i) := by
  choose D hD hval using fun i => scE_coord α s w hs hw i
  exact ⟨ContinuousLinearMap.pi D, hasFDerivAt_pi.mpr hD, fun a b i => hval i a b⟩

lemma scE_contDiffAt {m : ℕ} (α : ℝ) (s w : Fin m → ℝ) (hs : ∀ i, s i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    ContDiffAt ℝ 1 (fun p : (Fin m → ℝ) × (Fin m → ℝ) => scE α p.1 p.2) (s, w) := by
  refine contDiffAt_pi.mpr fun i => ?_
  let Ls : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ _ _)
  let Lw : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ _ _)
  have h1 : ContDiffAt ℝ 1 (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.2 i ^ α) (s, w) :=
    Lw.contDiff.contDiffAt.rpow_const_of_ne (hw i).ne'
  have h2 : ContDiffAt ℝ 1 (fun p : (Fin m → ℝ) × (Fin m → ℝ) => ((p.1 i)⁻¹) ^ 2) (s, w) :=
    (Ls.contDiff.contDiffAt.inv (hs i)).pow 2
  exact h1.mul h2


lemma pfw_mulVec_injective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) :
    Function.Injective A.mulVec := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hk : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    unfold Matrix.rank at hA; omega
  have hb : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hk
  have := LinearMap.ker_eq_bot.mp hb
  exact fun x y h => this h

lemma scN_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (e : Fin m → ℝ) (he : ∀ i, 0 < e i) : (scN A e).PosDef := by
  have hD : (diagonal e).PosDef := Matrix.posDef_diagonal_iff.mpr he
  have := hD.conjTranspose_mul_mul_same (pfw_mulVec_injective A hA)
  simpa [scN, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma scN_isUnit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n)
    (e : Fin m → ℝ) (he : ∀ i, 0 < e i) : IsUnit (scN A e).det :=
  isUnit_iff_ne_zero.mpr (scN_posDef A hA e he).det_pos.ne'

lemma scQm_psd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i) :
    (scQm A e).PosSemidef := by
  have hN : (scN A e).PosSemidef := by
    have hD : (diagonal e).PosSemidef := Matrix.PosSemidef.diagonal (fun i => he i)
    have := hD.conjTranspose_mul_mul_same A
    simpa [scN, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have := hN.inv.mul_mul_conjTranspose_same A
  simpa [scQm, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma scQm_idem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin m → ℝ)
    (hu : IsUnit (scN A e).det) : scQm A e * diagonal e * scQm A e = scQm A e := by
  unfold scQm
  have h : A * (scN A e)⁻¹ * Aᵀ * diagonal e * (A * (scN A e)⁻¹ * Aᵀ)
      = A * ((scN A e)⁻¹ * (Aᵀ * diagonal e * A) * (scN A e)⁻¹) * Aᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h, show Aᵀ * diagonal e * A = scN A e from rfl, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

/-- Rank-one update with the explicit leverage term. -/
lemma sc_det_affine {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin m → ℝ) (i : Fin m)
    (hM : IsUnit (Bᵀ * diagonal d * B).det) (c : ℝ) :
    (Bᵀ * diagonal (Function.update d i (d i + c)) * B).det =
      (Bᵀ * diagonal d * B).det * (1 + c * (B * (Bᵀ * diagonal d * B)⁻¹ * Bᵀ) i i) := by
  have hr1 : Bᵀ * diagonal (Function.update d i (d i + c)) * B =
      Bᵀ * diagonal d * B + replicateCol Unit (c • (fun k => B i k)) *
        replicateRow Unit (fun k => B i k) := by
    ext k l
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, diagonal_apply,
      replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.univ_unique, Finset.sum_singleton]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    have : ∑ x ∈ Finset.univ.erase i, B x k * Function.update d i (d i + c) x * B x l
        = ∑ x ∈ Finset.univ.erase i, B x k * d x * B x l := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    rw [this]
    ring
  rw [hr1, det_add_replicateCol_mul_replicateRow hM]
  congr 1
  rw [Matrix.det_unique]
  have : replicateCol Unit (c • (fun k => B i k)) = c • replicateCol Unit (fun k => B i k) := by
    ext; simp
  rw [this, Matrix.mul_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply_eq]
  congr 2

lemma sc_sum_update {m : ℕ} (f : Fin m → ℝ) (i : Fin m) (x : ℝ) :
    ∑ j, Function.update f i x j = ∑ j, f j - f i + x := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  ring

open PathFindingLP.WeightFunction in
/-- First-order condition: a minimizer satisfies `w_i = τ_i + β`. -/
theorem sc_foc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα : 0 < α) (s w : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (hw : IsRegularizedMinimizer A α β s w) (i : Fin m) :
    w i = scT A (scE α s w) i + β := by
  obtain ⟨hwpos, hmin⟩ := hw
  set B := diagonal (fun i => (s i)⁻¹) * A with hB
  set d : Fin m → ℝ := fun j => w j ^ α with hd
  have hdpos : ∀ j, 0 < d j := fun j => Real.rpow_pos_of_pos (hwpos j) α
  -- the matrix of fhat is N(e)
  have hMN : Bᵀ * diagonal d * B = scN A (scE α s w) := by
    rw [hB, scN, Matrix.transpose_mul, diagonal_transpose]
    have : Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal d * (diagonal (fun i => (s i)⁻¹) * A)
        = Aᵀ * (diagonal (fun i => (s i)⁻¹) * diagonal d * diagonal (fun i => (s i)⁻¹)) * A := by
      simp only [Matrix.mul_assoc]
    rw [this, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 3; funext j; simp only [scE, hd]; ring
  have he : ∀ j, 0 < scE α s w j := fun j =>
    mul_pos (Real.rpow_pos_of_pos (hwpos j) α) (pow_pos (inv_pos.mpr (hs j)) 2)
  have hMu : IsUnit (Bᵀ * diagonal d * B).det := by rw [hMN]; exact scN_isUnit A hA _ he
  set D := (Bᵀ * diagonal d * B).det with hD
  have hDpos : 0 < D := by rw [hD, hMN]; exact (scN_posDef A hA _ he).det_pos
  set q := (B * (Bᵀ * diagonal d * B)⁻¹ * Bᵀ) i i with hq
  -- q = s_i⁻² Q_ii
  have hqQ : w i ^ α * q = scT A (scE α s w) i := by
    rw [hq, hMN, scT, scQm, hB, Matrix.transpose_mul, diagonal_transpose]
    have : diagonal (fun i => (s i)⁻¹) * A * (scN A (scE α s w))⁻¹ *
        (Aᵀ * diagonal (fun i => (s i)⁻¹))
        = diagonal (fun i => (s i)⁻¹) * (A * (scN A (scE α s w))⁻¹ * Aᵀ) *
          diagonal (fun i => (s i)⁻¹) := by simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul, scE]
    ring
  -- the one-dimensional function
  let φ : ℝ → ℝ := fun t => fhat A α β s (Function.update w i (w i + t))
  have hφ : ∀ t, φ t = (∑ j, w j + t)
      - (1 / α) * Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q))
      - β * (∑ j, Real.log (w j) - Real.log (w i) + Real.log (w i + t)) := by
    intro t
    simp only [φ, fhat]
    have h1 : (fun j => Function.update w i (w i + t) j ^ α)
        = Function.update d i (d i + ((w i + t) ^ α - w i ^ α)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hd]
      · simp [Function.update_of_ne hj, hd]
    have h2 : (fun j => Real.log (Function.update w i (w i + t) j))
        = Function.update (fun j => Real.log (w j)) i (Real.log (w i + t)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h1, sc_det_affine B d i hMu, sc_sum_update, show (∑ j, Real.log (Function.update w i
      (w i + t) j)) = ∑ j, Function.update (fun j => Real.log (w j)) i (Real.log (w i + t)) j
      from by rw [← h2], sc_sum_update]
    ring
  -- local minimum at 0
  have hloc : IsLocalMin φ 0 := by
    have hmem : Set.Ioo (-w i) (w i) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [hwpos i]) (hwpos i)
    filter_upwards [hmem] with t ht
    have hpos : ∀ j, 0 < Function.update w i (w i + t) j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; linarith [ht.1]
      · rw [Function.update_of_ne hj]; exact hwpos j
    have h0 : φ 0 = fhat A α β s w := by simp [φ]
    rw [h0]; exact hmin _ hpos
  -- derivative at 0
  have hderiv : HasDerivAt φ (1 - (1 / α) * (D * (1 * α * w i ^ (α - 1) * q) / D)
      - β * (1 / w i)) 0 := by
    have hfun : φ = fun t => (∑ j, w j + t)
        - (1 / α) * Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q))
        - β * (∑ j, Real.log (w j) - Real.log (w i) + Real.log (w i + t)) := funext hφ
    rw [hfun]
    have hlin : HasDerivAt (fun t : ℝ => w i + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (w i)
    have hrp : HasDerivAt (fun t : ℝ => (w i + t) ^ α) (1 * α * (w i + 0) ^ (α - 1)) 0 :=
      hlin.rpow_const (Or.inl (by simp; exact (hwpos i).ne'))
    have hin : HasDerivAt (fun t : ℝ => D * (1 + ((w i + t) ^ α - w i ^ α) * q))
        (D * (1 * α * w i ^ (α - 1) * q)) 0 := by
      have := ((hrp.sub_const (w i ^ α)).mul_const q).const_add 1 |>.const_mul D
      simpa using this
    have hlog : HasDerivAt (fun t : ℝ => Real.log (D * (1 + ((w i + t) ^ α - w i ^ α) * q)))
        (D * (1 * α * w i ^ (α - 1) * q) / D) 0 := by
      have := hin.log (by simp; exact hDpos.ne')
      simpa using this
    have hlog2 : HasDerivAt (fun t : ℝ => Real.log (w i + t)) (1 / w i) 0 := by
      have := hlin.log (by simp; exact (hwpos i).ne')
      simpa using this
    have := (((hasDerivAt_id (0 : ℝ)).const_add (∑ j, w j)).sub
      (hlog.const_mul (1 / α))).sub
      ((hlog2.const_add (∑ j, Real.log (w j) - Real.log (w i))).const_mul β)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, id]
  have hzero := hloc.hasDerivAt_eq_zero hderiv
  have hwi := (hwpos i).ne'
  have hrp1 : w i ^ (α - 1) = w i ^ α / w i := Real.rpow_sub_one hwi α
  rw [hrp1] at hzero
  rw [← hqQ]
  field_simp at hzero
  linarith

/-- Calculus of `Φ` at a positive point. -/
lemma scPhi_calc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (s w : Fin m → ℝ) (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i) :
    ∃ P : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ),
      HasFDerivAt (scPhi A α β) P (s, w) ∧ ContDiffAt ℝ 1 (scPhi A α β) (s, w) ∧
      ∀ a b i, P (a, b) i = b i
        - (scE α s w i * (α * b i / w i - 2 * a i / s i) * scQm A (scE α s w) i i
          - scE α s w i * ∑ j, scE α s w j * (α * b j / w j - 2 * a j / s j)
              * scQm A (scE α s w) i j * scQm A (scE α s w) j i) := by
  have hs' : ∀ i, s i ≠ 0 := fun i => (hs i).ne'
  have he : ∀ i, 0 < scE α s w i := fun i =>
    mul_pos (Real.rpow_pos_of_pos (hw i) α) (pow_pos (inv_pos.mpr (hs i)) 2)
  have hu : IsUnit (scN A (scE α s w)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (scN_isUnit A hA _ he)
  obtain ⟨E', hE, hEv⟩ := scE_hasFDerivAt α s w hs' hw
  obtain ⟨T', hT, hTv⟩ := scT_hasFDerivAt A (scE α s w) hu
  have hsnd : HasFDerivAt (fun p : (Fin m → ℝ) × (Fin m → ℝ) => p.2)
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin m → ℝ)) (s, w) := hasFDerivAt_snd
  have hP := (hsnd.sub (hT.comp (s, w) hE)).sub_const (fun _ : Fin m => β)
  refine ⟨_, hP, ?_, fun a b i => ?_⟩
  · have hcd := (contDiffAt_snd.sub ((scT_contDiffAt A _ hu).comp (s, w)
      (scE_contDiffAt α s w hs' hw))).sub (contDiffAt_const (c := fun _ : Fin m => β))
    exact hcd
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', Pi.sub_apply]
    rw [hTv]
    simp only [hEv]

/-- Entry bound for a PSD matrix: `Q_ij² ≤ Q_ii Q_jj`. -/
lemma scpsd_sq_le {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosSemidef) (i j : Fin m) :
    Q i j ^ 2 ≤ Q i i * Q j j := by
  have h2 := hQ.submatrix ![i, j]
  have hd := h2.det_nonneg
  rw [Matrix.det_fin_two] at hd
  have hs : Q j i = Q i j := by
    have := hQ.isHermitian.apply i j
    simpa using this
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  rw [hs] at hd
  nlinarith

/-- The `K`-facts used by `sc_alg`, for `Q` PSD with `Q diag(e) Q = Q`. -/
lemma scK_facts {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) (e : Fin m → ℝ) (he : ∀ i, 0 ≤ e i)
    (hQ : Q.PosSemidef) (hidem : Q * diagonal e * Q = Q) :
    (∀ i, 0 ≤ e i * Q i i) ∧
    (∀ i j, 0 ≤ e i * e j * Q i j ^ 2) ∧
    (∀ i j, e i * e j * Q i j ^ 2 = e j * e i * Q j i ^ 2) ∧
    (∀ i, ∑ j, e i * e j * Q i j ^ 2 = e i * Q i i) ∧
    (∀ i j, e i * e j * Q i j ^ 2 ≤ (e i * Q i i) * (e j * Q j j)) ∧
    (∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, e i * e j * Q i j ^ 2 * v i * v j) := by
  have hs : ∀ i j, Q j i = Q i j := by
    intro i j
    have := hQ.isHermitian.apply i j
    simpa using this
  refine ⟨fun i => mul_nonneg (he i) hQ.diag_nonneg, fun i j => ?_, fun i j => ?_, fun i => ?_,
    fun i j => ?_, fun v => ?_⟩
  · exact mul_nonneg (mul_nonneg (he i) (he j)) (sq_nonneg _)
  · rw [hs i j]; ring
  · have h := congrFun (congrFun hidem i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_diagonal] at h
    rw [← h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [hs j i]; ring
  · have := scpsd_sq_le Q hQ i j
    have hij : 0 ≤ e i * e j := mul_nonneg (he i) (he j)
    calc e i * e j * Q i j ^ 2 ≤ e i * e j * (Q i i * Q j j) := mul_le_mul_of_nonneg_left this hij
      _ = (e i * Q i i) * (e j * Q j j) := by ring
  · have hH := hQ.hadamard hQ
    have key : ∑ i, ∑ j, e i * e j * Q i j ^ 2 * v i * v j
        = (fun i => e i * v i) ⬝ᵥ ((Q ⊙ Q) *ᵥ (fun i => e i * v i)) := by
      simp only [dotProduct, mulVec, hadamard, Finset.mul_sum, Matrix.of_apply]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    rw [key]
    simpa using hH.dotProduct_mulVec_nonneg (fun i => e i * v i)

open Finset

/-- Bilinear form `Q(u,w) = Σ u_i (τ_i w_i − Σ_j K_ij w_j)` (the Laplacian-like `Λ = diag τ − K`). -/
noncomputable def scQ {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ) (u w : Fin m → ℝ) : ℝ :=
  ∑ i, u i * (τ i * w i - ∑ j, K i j * w j)

lemma scQ_symm {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ) (hKs : ∀ i j, K i j = K j i)
    (u w : Fin m → ℝ) : scQ τ K u w = scQ τ K w u := by
  unfold scQ
  have h1 : ∑ i, u i * (τ i * w i - ∑ j, K i j * w j)
      = ∑ i, τ i * u i * w i - ∑ i, ∑ j, K i j * u i * w j := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
    rw [mul_sub, mul_sum]; congr 1; ring; apply sum_congr rfl; intro j _; ring
  have h2 : ∑ i, w i * (τ i * u i - ∑ j, K i j * u j)
      = ∑ i, τ i * w i * u i - ∑ i, ∑ j, K i j * w i * u j := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
    rw [mul_sub, mul_sum]; congr 1; ring; apply sum_congr rfl; intro j _; ring
  rw [h1, h2]
  congr 1
  · apply sum_congr rfl; intro i _; ring
  · rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    rw [hKs]; ring

lemma scQ_sub {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ) (u u' w : Fin m → ℝ) :
    scQ τ K (fun i => u i - u' i) w = scQ τ K u w - scQ τ K u' w := by
  unfold scQ; rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; ring

lemma scQ_sub_right {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ) (u w w' : Fin m → ℝ) :
    scQ τ K u (fun i => w i - w' i) = scQ τ K u w - scQ τ K u w' := by
  unfold scQ; rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
  have : ∑ j, K i j * (w j - w' j) = ∑ j, K i j * w j - ∑ j, K i j * w' j := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
  rw [this]; ring

lemma scQ_nonneg {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j) (hKs : ∀ i j, K i j = K j i) (hrow : ∀ i, ∑ j, K i j = τ i)
    (v : Fin m → ℝ) : 0 ≤ scQ τ K v v := by
  have key : 2 * scQ τ K v v = ∑ i, ∑ j, K i j * (v i - v j) ^ 2 := by
    unfold scQ
    have e1 : ∑ i, ∑ j, K i j * (v i - v j) ^ 2
        = ∑ i, ∑ j, K i j * v i ^ 2 + ∑ i, ∑ j, K i j * v j ^ 2
          - 2 * ∑ i, ∑ j, K i j * v i * v j := by
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]; apply sum_congr rfl; intro i _
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
    have e2 : ∑ i, ∑ j, K i j * v j ^ 2 = ∑ i, ∑ j, K i j * v i ^ 2 := by
      rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [hKs]
    have e3 : ∑ i, ∑ j, K i j * v i ^ 2 = ∑ i, τ i * v i ^ 2 := by
      apply sum_congr rfl; intro i _; rw [← hrow i, sum_mul]
    have e : ∑ i, v i * (τ i * v i - ∑ j, K i j * v j)
        = ∑ i, τ i * v i ^ 2 - ∑ i, ∑ j, K i j * v i * v j := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
      rw [mul_sub, mul_sum]; congr 1; ring; apply sum_congr rfl; intro j _; ring
    rw [e1, e2, e3, e]; ring
  have : 0 ≤ ∑ i, ∑ j, K i j * (v i - v j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hK0 i j) (sq_nonneg _)
  linarith

lemma scQ_le {m : ℕ} (τ : Fin m → ℝ) (K : Fin m → Fin m → ℝ)
    (hpsd : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, K i j * v i * v j) (v : Fin m → ℝ) :
    scQ τ K v v ≤ ∑ i, τ i * v i ^ 2 := by
  unfold scQ
  have e : ∑ i, v i * (τ i * v i - ∑ j, K i j * v j)
      = ∑ i, τ i * v i ^ 2 - ∑ i, ∑ j, K i j * v i * v j := by
    rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
    rw [mul_sub, mul_sum]; congr 1; ring; apply sum_congr rfl; intro j _; ring
  rw [e]; linarith [hpsd v]

/-- The algebraic core of Step Consistency. `z` solves `G z = Λ (y + α z)`; then
`‖y − c z‖_G ≤ ‖y‖_G` and `|y_i − c z_i| ≤ |y_i| + (1−α)⁻¹ ‖y‖_G`. -/
theorem sc_alg {m : ℕ} (g τ y z : Fin m → ℝ) (K : Fin m → Fin m → ℝ) (α c : ℝ)
    (hg : ∀ i, 0 < g i) (hτ0 : ∀ i, 0 ≤ τ i) (hτg : ∀ i, τ i ≤ g i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hKs : ∀ i j, K i j = K j i) (hrow : ∀ i, ∑ j, K i j = τ i)
    (hKle : ∀ i j, K i j ≤ τ i * τ j)
    (hpsd : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, K i j * v i * v j)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 - α)
    (hz : ∀ i, g i * z i = τ i * (y i + α * z i) - ∑ j, K i j * (y j + α * z j)) :
    PathFindingLP.WeightFunction.gNorm g (fun i => y i - c * z i)
        ≤ PathFindingLP.WeightFunction.gNorm g y ∧
      ∀ i, |y i - c * z i| ≤ |y i| + (1 - α)⁻¹ * PathFindingLP.WeightFunction.gNorm g y := by
  set v : Fin m → ℝ := fun i => y i + α * z i with hv
  have hΛ : ∀ i, τ i * v i - ∑ j, K i j * v j = g i * z i := fun i => (hz i).symm
  set Z := ∑ i, g i * z i ^ 2 with hZ
  set V := ∑ i, g i * v i ^ 2 with hV
  set Y := ∑ i, g i * y i ^ 2 with hY
  set qv := scQ τ K v v with hqv
  clear_value qv Y V Z v
  have hZ0 : 0 ≤ Z := hZ ▸ sum_nonneg fun i _ => mul_nonneg (hg i).le (sq_nonneg _)
  have hV0 : 0 ≤ V := hV ▸ sum_nonneg fun i _ => mul_nonneg (hg i).le (sq_nonneg _)
  have hY0 : 0 ≤ Y := hY ▸ sum_nonneg fun i _ => mul_nonneg (hg i).le (sq_nonneg _)
  -- Q(u, v) = Σ u_i g_i z_i
  have hQv : ∀ u, scQ τ K u v = ∑ i, g i * u i * z i := by
    intro u; unfold scQ; apply sum_congr rfl; intro i _; rw [hΛ i]; ring
  have hQzv : scQ τ K z v = Z := by rw [hQv, hZ]; apply sum_congr rfl; intro i _; ring
  have hqvV : qv = ∑ i, g i * v i * z i := by rw [hqv]; exact hQv v
  -- q(z) ≤ Z, q(v) ≤ V
  have hqz : scQ τ K z z ≤ Z := by
    rw [hZ]; refine (scQ_le τ K hpsd z).trans (sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (hτg i) (sq_nonneg _)
  have hqvle : qv ≤ V := by
    rw [hqv, hV]; refine (scQ_le τ K hpsd v).trans (sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (hτg i) (sq_nonneg _)
  have hqv0 : 0 ≤ qv := hqv ▸ scQ_nonneg τ K hK0 hKs hrow v
  -- Z ≤ qv from q(z - v) ≥ 0
  have hZq : Z ≤ qv := by
    have h0 := scQ_nonneg τ K hK0 hKs hrow (fun i => z i - v i)
    rw [scQ_sub, scQ_sub_right, scQ_sub_right, scQ_symm τ K hKs v z, hQzv, ← hqv] at h0
    linarith
  -- Σ g y z = qv - α Z
  have hyz : ∑ i, g i * y i * z i = qv - α * Z := by
    rw [hqvV, hZ, mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro i _
    simp only [hv]; ring
  -- G-norm part
  have hpart1 : ∑ i, g i * (y i - c * z i) ^ 2 ≤ Y := by
    have e : ∑ i, g i * (y i - c * z i) ^ 2 = Y - 2 * c * (∑ i, g i * y i * z i) + c ^ 2 * Z := by
      rw [hY, hZ, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [e, hyz]
    have h1 : c * (c + 2 * α) * Z ≤ c * 2 * Z := by
      apply mul_le_mul_of_nonneg_right _ hZ0
      apply mul_le_mul_of_nonneg_left _ hc0; linarith
    nlinarith [mul_le_mul_of_nonneg_left hZq hc0]
  -- V bound: (1-α)^2 V ≤ Y
  have hCS : qv ^ 2 ≤ V * Z := by
    rw [hqvV, hV, hZ]
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact mul_nonneg (hg i).le (sq_nonneg _)
    · intro i _; exact mul_nonneg (hg i).le (sq_nonneg _)
    · intro i _; apply le_of_eq; ring
  have hYexp : Y = V - 2 * α * qv + α ^ 2 * Z := by
    have hyv : ∀ i, y i = v i - α * z i := by intro i; simp only [hv]; ring
    rw [hY, hqvV, hV, hZ, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro i _; rw [hyv i]; ring
  have hVY : (1 - α) ^ 2 * V ≤ Y := by
    have h1 : (V - α * qv) ^ 2 ≤ Y * V := by
      rw [hYexp]; nlinarith [mul_le_mul_of_nonneg_left hCS (sq_nonneg α)]
    have h2 : (1 - α) * V ≤ V - α * qv := by nlinarith
    have h3 : 0 ≤ (1 - α) * V := mul_nonneg (by linarith) hV0
    have h4 : ((1 - α) * V) ^ 2 ≤ Y * V := (pow_le_pow_left₀ h3 h2 2).trans h1
    rcases hV0.eq_or_lt with h | h
    · rw [← h]; simpa using hY0
    · have : (1 - α) ^ 2 * V * V ≤ Y * V := by nlinarith
      exact le_of_mul_le_mul_right this h
  have hsqV : Real.sqrt V ≤ (1 - α)⁻¹ * Real.sqrt Y := by
    have h1α : 0 < 1 - α := by linarith
    rw [le_inv_mul_iff₀ h1α]
    have : Real.sqrt ((1 - α) ^ 2 * V) ≤ Real.sqrt Y := Real.sqrt_le_sqrt hVY
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1α.le] at this
  -- |(K v)_i| ≤ τ_i √V
  have hKv : ∀ i, |∑ j, K i j * v j| ≤ τ i * Real.sqrt V := by
    intro i
    have h1 : (∑ j, K i j * v j) ^ 2 ≤ (∑ j, K i j) * ∑ j, K i j * v j ^ 2 := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro j _; exact hK0 i j
      · intro j _; exact mul_nonneg (hK0 i j) (sq_nonneg _)
      · intro j _; apply le_of_eq; ring
    have h2 : ∑ j, K i j * v j ^ 2 ≤ τ i * V := by
      rw [hV, mul_sum]; apply sum_le_sum; intro j _
      have : K i j ≤ τ i * g j := (hKle i j).trans (mul_le_mul_of_nonneg_left (hτg j) (hτ0 i))
      nlinarith [sq_nonneg (v j)]
    rw [hrow i] at h1
    have h3 : (∑ j, K i j * v j) ^ 2 ≤ (τ i * Real.sqrt V) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hV0]
      nlinarith [mul_le_mul_of_nonneg_left h2 (hτ0 i)]
    exact abs_le_of_sq_le_sq' h3 (mul_nonneg (hτ0 i) (Real.sqrt_nonneg _)) |> fun h =>
      abs_le.mpr ⟨h.1, h.2⟩
  refine ⟨?_, ?_⟩
  · show Real.sqrt (∑ i, g i * (y i - c * z i) ^ 2) ≤ Real.sqrt (∑ i, g i * y i ^ 2)
    rw [← hY]; exact Real.sqrt_le_sqrt hpart1
  · intro i
    have hD : 0 < g i - α * τ i := by nlinarith [hτg i, hτ0 i, hg i]
    have hcτ : c * τ i ≤ g i - α * τ i := by nlinarith [hτg i, hτ0 i]
    have hDz : (g i - α * τ i) * z i = τ i * y i - ∑ j, K i j * v j := by
      have := hz i; simp only [hv] at this ⊢; linarith
    have hmul : (g i - α * τ i) * (y i - c * z i)
        = (g i - α * τ i - c * τ i) * y i + c * ∑ j, K i j * v j := by
      have : (g i - α * τ i) * (y i - c * z i)
          = (g i - α * τ i) * y i - c * ((g i - α * τ i) * z i) := by ring
      rw [this, hDz]; ring
    have hbound : |(g i - α * τ i) * (y i - c * z i)|
        ≤ (g i - α * τ i) * (|y i| + Real.sqrt V) := by
      rw [hmul]
      calc |(g i - α * τ i - c * τ i) * y i + c * ∑ j, K i j * v j|
          ≤ |(g i - α * τ i - c * τ i) * y i| + |c * ∑ j, K i j * v j| := abs_add_le _ _
        _ = (g i - α * τ i - c * τ i) * |y i| + c * |∑ j, K i j * v j| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hc0]
        _ ≤ (g i - α * τ i - c * τ i) * |y i| + c * (τ i * Real.sqrt V) := by
            gcongr; exact hKv i
        _ ≤ (g i - α * τ i) * (|y i| + Real.sqrt V) := by
            have h1 := abs_nonneg (y i)
            have h2 := Real.sqrt_nonneg V
            have h3 := mul_le_mul_of_nonneg_right hcτ h2
            have h4 := mul_nonneg (mul_nonneg hc0 (hτ0 i)) h1
            linarith
    rw [abs_mul, abs_of_pos hD] at hbound
    have h1 : |y i - c * z i| ≤ |y i| + Real.sqrt V := le_of_mul_le_mul_left (a := g i - α * τ i) hbound hD
    show |y i - c * z i| ≤ |y i| + (1 - α)⁻¹ * Real.sqrt (∑ i, g i * y i ^ 2)
    rw [← hY]; linarith

/-! ## Directional derivative of `Φ` and positivity -/

lemma scPhi_dir {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α : ℝ) (s w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) (P : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ))
    (hval : ∀ a b i, P (a, b) i = b i
        - (scE α s w i * (α * b i / w i - 2 * a i / s i) * scQm A (scE α s w) i i
          - scE α s w i * ∑ j, scE α s w j * (α * b j / w j - 2 * a j / s j)
              * scQm A (scE α s w) i j * scQm A (scE α s w) j i))
    (hsym : ∀ i j, scQm A (scE α s w) j i = scQm A (scE α s w) i j)
    (h : Fin m → ℝ) (i : Fin m) :
    P (0, h) i = w i * (h i / w i) - α * (scT A (scE α s w) i * (h i / w i)
      - ∑ j, scE α s w i * scE α s w j * scQm A (scE α s w) i j ^ 2 * (h j / w j)) := by
  rw [hval]
  simp only [Pi.zero_apply, mul_zero, zero_div, sub_zero]
  have e1 : scE α s w i * ∑ j, scE α s w j * (α * h j / w j) * scQm A (scE α s w) i j
        * scQm A (scE α s w) j i
      = α * ∑ j, scE α s w i * scE α s w j * scQm A (scE α s w) i j ^ 2 * (h j / w j) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [hsym i j]; ring
  rw [e1, scT]
  have hwi := (hw i).ne'
  field_simp

lemma scPhi_quad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α : ℝ)
    (hα0 : 0 ≤ α) (s w : Fin m → ℝ) (hs : ∀ i, 0 < s i) (hw : ∀ i, 0 < w i)
    (P : ((Fin m → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ))
    (hval : ∀ a b i, P (a, b) i = b i
        - (scE α s w i * (α * b i / w i - 2 * a i / s i) * scQm A (scE α s w) i i
          - scE α s w i * ∑ j, scE α s w j * (α * b j / w j - 2 * a j / s j)
              * scQm A (scE α s w) i j * scQm A (scE α s w) j i))
    (h : Fin m → ℝ) :
    ∑ i, (w i - α * scT A (scE α s w) i) * (h i / w i) ^ 2 ≤ ∑ i, (h i / w i) * P (0, h) i := by
  set e := scE α s w with he_def
  have he' : ∀ i, 0 < e i := fun i =>
    mul_pos (Real.rpow_pos_of_pos (hw i) α) (pow_pos (inv_pos.mpr (hs i)) 2)
  have he : ∀ i, 0 ≤ e i := fun i => (he' i).le
  have hQ := scQm_psd A e he
  have hidem := scQm_idem A e (scN_isUnit A hA e he')
  obtain ⟨-, -, -, -, -, hpsd⟩ := scK_facts (scQm A e) e he hQ hidem
  have hsym : ∀ i j, scQm A e j i = scQm A e i j := by
    intro i j
    have := hQ.isHermitian.apply i j
    simpa using this
  have hx : ∑ i, (h i / w i) * P (0, h) i = ∑ i, w i * (h i / w i) ^ 2
      - α * scQ (fun i => e i * scQm A e i i) (fun i j => e i * e j * scQm A e i j ^ 2)
          (fun i => h i / w i) (fun i => h i / w i) := by
    unfold scQ
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [scPhi_dir A α s w hw P hval hsym h i]
    simp only [scT, ← he_def]
    have : ∑ j, e i * e j * scQm A e i j ^ 2 * (h j / w j)
        = ∑ j, (fun i j => e i * e j * scQm A e i j ^ 2) i j * (fun i => h i / w i) j := rfl
    rw [this]
    ring
  have hle := scQ_le (fun i => e i * scQm A e i i) (fun i j => e i * e j * scQm A e i j ^ 2)
    hpsd (fun i => h i / w i)
  rw [hx]
  have hsplit : ∑ i, (w i - α * scT A e i) * (h i / w i) ^ 2
      = ∑ i, w i * (h i / w i) ^ 2 - α * ∑ i, (e i * scQm A e i i) * (h i / w i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; simp only [scT]; ring
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left hle hα0
  linarith

/-- Positive zeros of `Φ(s, ·)` are unique. -/
theorem sc_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 < β) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i)
    (w1 w2 : Fin m → ℝ) (hw1 : ∀ i, 0 < w1 i) (hw2 : ∀ i, 0 < w2 i)
    (h1 : scPhi A α β (s, w1) = 0) (h2 : scPhi A α β (s, w2) = 0) : w1 = w2 := by
  by_contra hne
  set h : Fin m → ℝ := w2 - w1 with hh
  have hhne : ∃ i, h i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    funext i
    have := hcon i
    simp only [hh, Pi.sub_apply] at this
    linarith
  let wt : ℝ → Fin m → ℝ := fun t => w1 + t • h
  have hwt_apply : ∀ t i, wt t i = w1 i + t * h i := fun t i => rfl
  have hwt : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ i, 0 < wt t i := by
    intro t ht i
    rw [hwt_apply]
    simp only [hh, Pi.sub_apply]
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have := mul_pos (sub_pos.mpr hlt) (hw1 i)
      nlinarith [mul_nonneg ht.1 (hw2 i).le]
    · rw [heq]; linarith [hw2 i]
  let ψ : ℝ → ℝ := fun t => ∑ i, h i * (scPhi A α β (s, wt t) i / wt t i)
  have hderiv : ∀ t, (∀ i, 0 < wt t i) →
      ∃ D, HasDerivAt ψ D t ∧ β * ∑ i, (h i / wt t i) ^ 2 ≤ D := by
    intro t hpos
    obtain ⟨P, hP, -, hval⟩ := scPhi_calc A hA α β s (wt t) hs hpos
    have hcurve : HasDerivAt (fun τ : ℝ => ((s, wt τ) : (Fin m → ℝ) × (Fin m → ℝ)))
        ((0 : Fin m → ℝ), h) t := by
      refine (hasDerivAt_const t s).prodMk ?_
      have := ((hasDerivAt_id t).smul_const h).const_add w1
      simpa [wt] using this
    have hcomp : HasDerivAt (scPhi A α β ∘ fun τ => ((s, wt τ) : (Fin m → ℝ) × (Fin m → ℝ)))
        (P (0, h)) t :=
      HasFDerivAt.comp_hasDerivAt t hP hcurve
    have hi : ∀ i ∈ Finset.univ, HasDerivAt (fun τ => h i * (scPhi A α β (s, wt τ) i / wt τ i))
        (h i * ((P (0, h) i * wt t i - scPhi A α β (s, wt t) i * h i) / (wt t i) ^ 2)) t := by
      intro i _
      have hc := hasDerivAt_pi.mp hcomp i
      have hd : HasDerivAt (fun τ => wt τ i) (h i) t := by
        have := ((hasDerivAt_id t).mul_const (h i)).const_add (w1 i)
        simpa [hwt_apply] using this
      exact (hc.div hd (hpos i).ne').const_mul (h i)
    refine ⟨_, HasDerivAt.fun_sum hi, ?_⟩
    have hq := scPhi_quad A hA α hα0 s (wt t) hs hpos P hval h
    have hΦ : ∀ i, scPhi A α β (s, wt t) i = wt t i - scT A (scE α s (wt t)) i - β := by
      intro i; simp [scPhi]
    have hrw : ∑ i, h i * ((P (0, h) i * wt t i - scPhi A α β (s, wt t) i * h i) / wt t i ^ 2)
        = ∑ i, (h i / wt t i) * P (0, h) i
          - ∑ i, (wt t i - scT A (scE α s (wt t)) i - β) * (h i / wt t i) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [hΦ]
      have := (hpos i).ne'
      field_simp
    rw [hrw]
    have he : ∀ i, 0 ≤ scE α s (wt t) i := fun i =>
      (mul_pos (Real.rpow_pos_of_pos (hpos i) α) (pow_pos (inv_pos.mpr (hs i)) 2)).le
    have hτ0 : ∀ i, 0 ≤ scT A (scE α s (wt t)) i := fun i =>
      mul_nonneg (he i) (scQm_psd A _ he).diag_nonneg
    have hterm : β * ∑ i, (h i / wt t i) ^ 2
        ≤ ∑ i, (wt t i - α * scT A (scE α s (wt t)) i) * (h i / wt t i) ^ 2
          - ∑ i, (wt t i - scT A (scE α s (wt t)) i - β) * (h i / wt t i) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum; intro i _
      have h3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hα1) (hτ0 i)) (sq_nonneg (h i / wt t i))
      nlinarith [h3]
    linarith
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun t ht =>
    (hderiv t (hwt t ht)).choose_spec.1.continuousAt.continuousWithinAt
  have hpos' : ∀ t ∈ interior (Set.Icc (0:ℝ) 1), 0 < deriv ψ t := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨D, hD, hDle⟩ := hderiv t (hwt t (Set.Ioo_subset_Icc_self ht))
    rw [hD.deriv]
    obtain ⟨i, hi⟩ := hhne
    have hwti := (hwt t (Set.Ioo_subset_Icc_self ht) i).ne'
    have hxi : 0 < (h i / wt t i) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (div_ne_zero hi hwti)))
    have hsum : 0 < ∑ j, (h j / wt t j) ^ 2 :=
      lt_of_lt_of_le hxi (Finset.single_le_sum (fun j _ => sq_nonneg (h j / wt t j))
        (Finset.mem_univ i))
    nlinarith [mul_pos hβ hsum]
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont hpos'
  have hlt := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_lt_one
  have hw0 : wt 0 = w1 := by funext i; rw [hwt_apply]; ring
  have hw1' : wt 1 = w2 := by funext i; rw [hwt_apply]; simp only [hh, Pi.sub_apply]; ring
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ, hw0, h1, Pi.zero_apply, zero_div, mul_zero, Finset.sum_const_zero]
  have hψ1 : ψ 1 = 0 := by
    simp only [ψ, hw1', h2, Pi.zero_apply, zero_div, mul_zero, Finset.sum_const_zero]
  linarith

/-- Differentiability of the minimizer map and the linearized first-order condition. -/
theorem sc_diff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : A.rank = n) (α β : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 < β) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → (∀ i, 0 < g s i) ∧ scPhi A α β (s, g s) = 0)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) :
    DifferentiableAt ℝ g s ∧ ∀ a i, (fderiv ℝ g s a) i
        - (scE α s (g s) i * (α * (fderiv ℝ g s a) i / g s i - 2 * a i / s i)
            * scQm A (scE α s (g s)) i i
          - scE α s (g s) i * ∑ j, scE α s (g s) j
              * (α * (fderiv ℝ g s a) j / g s j - 2 * a j / s j)
              * scQm A (scE α s (g s)) i j * scQm A (scE α s (g s)) j i) = 0 := by
  obtain ⟨hgpos, hg0⟩ := hg s hs
  obtain ⟨P, hP, hcd, hval⟩ := scPhi_calc A hA α β s (g s) hs hgpos
  set L := P ∘L ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m → ℝ) with hL
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun h hzero => ?_
    have hP0 : P (0, h) = 0 := hzero
    have hq := scPhi_quad A hA α hα0 s (g s) hs hgpos P hval h
    simp only [hP0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hq
    have hτ : ∀ i, scT A (scE α s (g s)) i = g s i - β := by
      intro i
      have := congrFun hg0 i
      simp only [scPhi, Pi.sub_apply, Pi.zero_apply] at this
      linarith
    have hc : ∀ i, 0 < g s i - α * scT A (scE α s (g s)) i := by
      intro i; rw [hτ]; nlinarith [hgpos i]
    have hterm : ∀ i ∈ Finset.univ,
        0 ≤ (g s i - α * scT A (scE α s (g s)) i) * (h i / g s i) ^ 2 :=
      fun i _ => mul_nonneg (hc i).le (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
      (le_antisymm hq (Finset.sum_nonneg hterm))
    funext i
    have hi := hz i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hi with h0 | h0
    · exact absurd h0 (hc i).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
      rw [div_eq_zero_iff] at this
      rcases this with h3 | h3
      · simpa using h3
      · exact absurd h3 (hgpos i).ne'
  have hbij : Function.Bijective L :=
    ⟨hinj, LinearMap.surjective_of_injective (f := (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) hinj⟩
  have hinv : L.IsInvertible :=
    ⟨(LinearEquiv.ofBijective (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) hbij).toContinuousLinearEquiv,
      by ext; rfl⟩
  have if₂ : (fderiv ℝ (scPhi A α β) (s, g s) ∘L
      ContinuousLinearMap.inr ℝ (Fin m → ℝ) (Fin m → ℝ)).IsInvertible := by
    rw [hP.fderiv]; exact hinv
  set ψ := hcd.implicitFunction one_ne_zero if₂ with hψ_def
  have hψs : ψ s = g s := hcd.implicitFunction_apply_self one_ne_zero if₂
  have hψeq := hcd.eventually_apply_implicitFunction one_ne_zero if₂
  have hψcd : ContDiffAt ℝ 1 ψ s := hcd.contDiffAt_implicitFunction one_ne_zero if₂
  have hopen : IsOpen {w : Fin m → ℝ | ∀ i, 0 < w i} := by
    have : {w : Fin m → ℝ | ∀ i, 0 < w i} = ⋂ i, {w : Fin m → ℝ | 0 < w i} := by
      ext w; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hψpos : ∀ᶠ x in nhds s, ∀ i, 0 < ψ x i := by
    have hmem : {w : Fin m → ℝ | ∀ i, 0 < w i} ∈ nhds (ψ s) := by
      rw [hψs]; exact hopen.mem_nhds hgpos
    exact hψcd.continuousAt.preimage_mem_nhds hmem
  have hspos : ∀ᶠ x in nhds s, ∀ i, 0 < x i := hopen.mem_nhds hs
  have hgeq : g =ᶠ[nhds s] ψ := by
    filter_upwards [hψeq, hψpos, hspos] with x hx1 hx2 hx3
    obtain ⟨hgx, hgx0⟩ := hg x hx3
    exact sc_unique A hA α β hα0 hα1.le hβ x hx3 (g x) (ψ x) hgx hx2 hgx0 (hx1.trans hg0)
  have hdiff : DifferentiableAt ℝ g s :=
    (hψcd.differentiableAt one_ne_zero).congr_of_eventuallyEq hgeq
  refine ⟨hdiff, fun a i => ?_⟩
  have hcompo : HasFDerivAt (scPhi A α β ∘ fun x => ((id x, g x) : (Fin m → ℝ) × (Fin m → ℝ)))
      (P ∘L ((ContinuousLinearMap.id ℝ (Fin m → ℝ)).prod (fderiv ℝ g s))) s :=
    HasFDerivAt.comp s hP ((hasFDerivAt_id s).prodMk hdiff.hasFDerivAt)
  have hzero : HasFDerivAt (scPhi A α β ∘ fun x => ((id x, g x) : (Fin m → ℝ) × (Fin m → ℝ)))
      (0 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) s := by
    refine (hasFDerivAt_const (0 : Fin m → ℝ) s).congr_of_eventuallyEq ?_
    filter_upwards [hspos] with x hx
    exact (hg x hx).2
  have huniq := hcompo.unique hzero
  have := congrArg (fun T : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => T a i) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, Pi.zero_apply] at this
  rw [hval] at this
  exact this

open PathFindingLP.WeightFunction in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank = n) (hn : 0 < n) (hnm : n < m) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
      IsRegularizedMinimizer A (thm1Alpha A) (thm1Beta A) s (g s)) :
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s) ∧
      IsStepConsistent g (2 * Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ))) := by
  set L := Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ)) with hL
  have hmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrank : (A.rank : ℝ) = n := by exact_mod_cast hA
  have hL1 : 1 < L := by
    rw [hL, hrank]
    have h2 : (2 : ℝ) < 2 * m / n := by rw [lt_div_iff₀ hnR]; linarith
    have := Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) (by norm_num) h2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  set α := thm1Alpha A with hα
  set β := thm1Beta A with hβ
  have hαL : α = 1 - L⁻¹ := by rw [hα]; rfl
  have hLpos : 0 < L := by linarith
  have hα0 : 0 < α := by
    rw [hαL]; have := inv_lt_one_of_one_lt₀ hL1; linarith
  have hα1 : α < 1 := by
    rw [hαL]; have : 0 < L⁻¹ := inv_pos.mpr hLpos; linarith
  have h1α : (1 - α)⁻¹ = L := by rw [hαL]; simp
  have hβ0 : 0 < β := by
    rw [hβ, thm1Beta, hrank]; exact div_pos hnR (by linarith)
  have hfoc : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) →
      (∀ i, 0 < g s i) ∧ scPhi A α β (s, g s) = 0 := by
    intro s hs
    refine ⟨(hg s hs).1, ?_⟩
    funext i
    have := sc_foc A hA α β hα0 s (g s) hs (hg s hs) i
    simp only [scPhi, Pi.sub_apply, Pi.zero_apply]
    linarith
  have hD := fun s hs => sc_diff A hA α β hα0.le hα1 hβ0 g hfoc s hs
  refine ⟨fun s hs => (hD s hs).1, ?_⟩
  unfold IsStepConsistent
  refine ⟨by linarith, fun s hs r hr y => ?_⟩
  obtain ⟨hgpos, -⟩ := hfoc s hs
  have hrel := (hD s hs).2 (fun j => s j * y j)
  have hfoc_s := sc_foc A hA α β hα0 s (g s) hs (hg s hs)
  set w := g s with hw
  set e := scE α s w with he_def
  set Q := scQm A e with hQ_def
  set b := fderiv ℝ g s (fun j => s j * y j) with hb
  set z : Fin m → ℝ := fun i => -(1/2) * (b i / w i) with hz_def
  have he' : ∀ i, 0 < e i := fun i =>
    mul_pos (Real.rpow_pos_of_pos (hgpos i) α) (pow_pos (inv_pos.mpr (hs i)) 2)
  have hQpsd := scQm_psd A e (fun i => (he' i).le)
  have hidem := scQm_idem A e (scN_isUnit A hA e he')
  obtain ⟨hτ0, hK0, hKs, hrow, hKle, hpsd⟩ :=
    scK_facts Q e (fun i => (he' i).le) hQpsd hidem
  have hsym : ∀ i j, Q j i = Q i j := by
    intro i j; have := hQpsd.isHermitian.apply i j; simpa using this
  have hτ : ∀ i, e i * Q i i = w i - β := by
    intro i; have := hfoc_s i; simp only [scT] at this; linarith
  have hsub : ∀ j, α * b j / w j - 2 * (s j * y j) / s j = -2 * (y j + α * z j) := by
    intro j
    have h1 := (hgpos j).ne'
    have h2 := (hs j).ne'
    simp only [hz_def]
    field_simp
    ring
  have hzeq : ∀ i, w i * z i = (e i * Q i i) * (y i + α * z i)
      - ∑ j, e i * e j * Q i j ^ 2 * (y j + α * z j) := by
    intro i
    have h0 := hrel i
    beta_reduce at h0
    have hsum : ∑ j, e j * (α * b j / w j - 2 * (s j * y j) / s j) * Q i j * Q j i
        = -2 * ∑ j, e j * Q i j ^ 2 * (y j + α * z j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [hsub j, hsym i j]; ring
    rw [hsum, hsub i] at h0
    have hK : ∑ j, e i * e j * Q i j ^ 2 * (y j + α * z j)
        = e i * ∑ j, e j * Q i j ^ 2 * (y j + α * z j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have hwz : w i * z i = -(1/2) * b i := by
      simp only [hz_def]; have := (hgpos i).ne'; field_simp
    rw [hK, hwz]
    linear_combination (-1/2 : ℝ) * h0
  have hc0 : 0 ≤ 2 / r := div_nonneg (by norm_num) (by linarith)
  have hc1 : 2 / r ≤ 1 - α := by
    rw [hαL, sub_sub_cancel, div_le_iff₀ (by linarith)]
    rw [inv_mul_eq_div, le_div_iff₀ hLpos]
    linarith
  have hτg : ∀ i, e i * Q i i ≤ w i := fun i => by rw [hτ]; linarith
  obtain ⟨hA1, hA2⟩ := sc_alg w (fun i => e i * Q i i) y z (fun i j => e i * e j * Q i j ^ 2)
    α (2 / r) hgpos hτ0 hτg hK0 hKs hrow hKle hpsd hα0.le hα1 hc0 hc1 hzeq
  have hstep : consistencyStep g s r y = fun i => y i - 2 / r * z i := by
    funext i
    simp only [consistencyStep, hz_def]
    ring
  rw [hstep]
  refine ⟨hA1, ?_⟩
  have hgn : 0 ≤ gNorm w y := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg
    (add_nonneg (norm_nonneg _) (mul_nonneg (by linarith) hgn))).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have h2 := hA2 i
  rw [h1α] at h2
  have hyi : |y i| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i
  nlinarith [mul_nonneg hLpos.le hgn]
