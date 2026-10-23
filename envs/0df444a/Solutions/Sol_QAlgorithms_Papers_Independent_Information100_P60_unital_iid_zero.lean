-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.unital_iid_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:29:52.983615+00:00
-- url     : https://prove2.me/submissions/38651991-d6fb-4c43-aed0-0f6924b88267

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

-- ===== P60A.lean

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma kraus_psd {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) {X : Mat (Fin d)}
    (hX : X.PosSemidef) : (N X).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [hE, krausApply]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (E j)

lemma kraus_trace {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) (X : Mat (Fin d)) :
    (N X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := hN
  rw [hE, krausApply, Matrix.trace_sum]
  have : ∀ j, (E j * X * (E j)ᴴ).trace = ((E j)ᴴ * E j * X).trace := fun j => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hK, Matrix.one_mul]

lemma perm_unitary (σ : Equiv.Perm (Fin d)) :
    (σ.permMatrix ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

lemma perm_conj_diag (σ : Equiv.Perm (Fin d)) (l : Fin d → ℂ) :
    σ.permMatrix ℂ * Matrix.diagonal l * (σ.permMatrix ℂ)ᴴ = Matrix.diagonal (l ∘ σ) := by
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.diagonal_apply, Equiv.Perm.inv_def, σ.injective.eq_iff]


lemma single_psd (j : Fin d) : (Matrix.single j j (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single]
  refine Matrix.PosSemidef.diagonal fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma unital_sim (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (ρ : Mat (Fin d)) (hρ : ρ.PosSemidef) :
    ∃ c : Equiv.Perm (Fin d) → ℝ, ∃ U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ,
      (∀ σ, 0 ≤ c σ) ∧ ∑ σ, c σ = 1 ∧
      N ρ = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * ρ * (U σ : Mat (Fin d))ᴴ) := by
  have hH := hρ.1
  have hS := (kraus_psd hN hρ).1
  have hVm := hH.eigenvectorUnitary.2
  have hWm := hS.eigenvectorUnitary.2
  set V : Mat (Fin d) := (hH.eigenvectorUnitary : Mat (Fin d)) with hV
  set W : Mat (Fin d) := (hS.eigenvectorUnitary : Mat (Fin d)) with hW
  set l := hH.eigenvalues
  set μ := hS.eigenvalues
  have hVV : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self _
  have hWW : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  have hρV : ρ = V * Matrix.diagonal (RCLike.ofReal ∘ l) * Vᴴ := by
    have := hH.spectral_theorem; rw [Unitary.conjStarAlgAut_apply] at this; exact this
  have hNW : Wᴴ * N ρ * W = Matrix.diagonal (RCLike.ofReal ∘ μ) := by
    have := hS.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this; exact this
  set Mx : Fin d → Mat (Fin d) := fun j => Wᴴ * N (V * Matrix.single j j 1 * Vᴴ) * W with hMx
  have hMpsd : ∀ j, (Mx j).PosSemidef := fun j =>
    (kraus_psd hN ((single_psd j).mul_mul_conjTranspose_same V)).conjTranspose_mul_mul_same W
  have hsum : ∑ j, Mx j = 1 := by
    simp only [hMx, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum]
    rw [Matrix.sum_single_one, Matrix.mul_one, hVV', hu, Matrix.mul_one, hWW]
  have htr : ∀ j, (Mx j).trace = 1 := fun j => by
    simp only [hMx]
    rw [Matrix.trace_mul_cycle, hWW', Matrix.one_mul, kraus_trace hN, Matrix.trace_mul_cycle,
      hVV, Matrix.one_mul, Matrix.trace_single_eq_same]
  have hdec : Wᴴ * N ρ * W = ∑ j, ((l j : ℝ) : ℂ) • Mx j := by
    have : ρ = ∑ j, ((l j : ℝ) : ℂ) • (V * Matrix.single j j 1 * Vᴴ) := by
      rw [hρV, ← Matrix.sum_single_eq_diagonal]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : ∀ a : ℂ, Matrix.single j j a = a • Matrix.single j j (1:ℂ) := fun a => by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [this, map_sum]
    simp only [map_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, hMx]
  have hμ : ∀ i, μ i = ∑ j, l j * (Mx j i i).re := fun i => by
    have := congrArg (fun A => (A i i).re) (hNW.symm.trans hdec)
    simpa [Matrix.sum_apply] using this
  set D : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (Mx j i i).re with hD
  have hDs : D ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · exact (Complex.nonneg_iff.mp ((hMpsd j).diag_nonneg)).1
    · have := congrArg (fun A => (A i i).re) hsum
      simpa [hD, Matrix.sum_apply] using this
    · have := congrArg Complex.re (htr j)
      simpa [hD, Matrix.trace] using this
  obtain ⟨c, hc0, hc1, hcD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hDs
  have hμ' : ∀ i, μ i = ∑ σ, c σ * l (σ i) := fun i => by
    rw [hμ]
    have : ∀ j, (Mx j i i).re = D i j := fun j => rfl
    simp_rw [this, ← hcD, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_comm]
  have hUm : ∀ σ : Equiv.Perm (Fin d), W * σ.permMatrix ℂ * Vᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    fun σ => Submonoid.mul_mem _ (Submonoid.mul_mem _ hWm (perm_unitary σ))
      (by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hVm)
  refine ⟨c, fun σ => ⟨_, hUm σ⟩, hc0, hc1, ?_⟩
  have hNρ : N ρ = W * Matrix.diagonal (RCLike.ofReal ∘ μ) * Wᴴ := by
    rw [← hNW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW', Matrix.one_mul, Matrix.mul_assoc,
      hWW', Matrix.mul_one]
  have hterm : ∀ σ : Equiv.Perm (Fin d),
      (W * σ.permMatrix ℂ * Vᴴ) * ρ * (W * σ.permMatrix ℂ * Vᴴ)ᴴ =
        W * Matrix.diagonal ((RCLike.ofReal ∘ l) ∘ σ) * Wᴴ := fun σ => by
    rw [← perm_conj_diag, hρV]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hVV,
      Matrix.one_mul]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ μ : Fin d → ℂ) =
      ∑ σ, ((c σ : ℝ) : ℂ) • Matrix.diagonal ((RCLike.ofReal ∘ l : Fin d → ℂ) ∘ σ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply]
    split_ifs with h
    · rw [hμ']
      push_cast
      simp [smul_eq_mul]
    · simp
  simp only [hterm]
  rw [hNρ, hdiag, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

end X4P60

end

-- ===== P60B.lean

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- The mixed-unitary map as a continuous linear map. -/
def mixMap (c : Equiv.Perm (Fin d) → ℝ) (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) :
    Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixMap_apply (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (X : Mat (Fin d)) :
    mixMap c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixMap_mem (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (hc0 : ∀ σ, 0 ≤ c σ)
    (hc1 : ∑ σ, c σ = 1) : mixMap c U ∈ MU d := by
  set e := (Fintype.equivFin (Equiv.Perm (Fin d))).symm
  refine ⟨?_, Fintype.card (Equiv.Perm (Fin d)), c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card (Equiv.Perm (Fin d)),
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixMap_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixMap_apply, ← Equiv.sum_comp e]
    rfl

/-- embedding of `Fin d` into the registers for `r = k = 1`. -/
def fe (a : Fin d) : Reg 1 d 1 := (fun _ => 0, fun _ => a)
def ge (p : Reg 1 d 1) : Fin d := p.2 0

lemma ge_fe (a : Fin d) : ge (fe a) = a := rfl
lemma fe_ge (p : Reg 1 d 1) : fe (ge p) = p := by
  obtain ⟨p1, p2⟩ := p
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext i
  rw [Subsingleton.elim i 0]
  rfl

def eq1 : Fin d ≃ Reg 1 d 1 where
  toFun := fe
  invFun := ge
  left_inv := ge_fe
  right_inv := fe_ge

lemma output_eq (Φ : Maps d d) (X : Mat (Reg 1 d 1)) :
    output 1 1 Φ X = (Φ (X.submatrix fe fe)).submatrix ge ge := by
  ext p q
  rw [← fe_ge p, ← fe_ge q]
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, Matrix.submatrix_apply,
    Fin.prod_univ_one]
  conv_rhs => rw [Matrix.matrix_eq_sum_single (X.submatrix fe fe)]
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs : Matrix.single a b (X.submatrix fe fe a b) = (X.submatrix fe fe a b) • Matrix.single a b 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, Matrix.smul_apply, smul_eq_mul]
  rfl

lemma trace_ge (A : Mat (Fin d)) : (A.submatrix ge ge).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1.symm _ _ (fun p => rfl)

lemma trace_fe (A : Mat (Reg 1 d 1)) : (A.submatrix fe fe).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1 _ _ (fun p => rfl)

lemma trace_copies {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) (Y : Mat I) :
    (copies m Y).trace = Y.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, copies, Matrix.of_apply]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

end X4P60

end

-- ===== P60C.lean

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma sim_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (X : Mat (Reg 1 d 1)) (hX : X.PosSemidef) :
    ∃ Phi ∈ MU d, output 1 1 Phi X = output 1 1 N X := by
  obtain ⟨c, U, hc0, hc1, h⟩ := unital_sim N hN hu _ (hX.submatrix fe)
  refine ⟨mixMap c U, mixMap_mem c U hc0 hc1, ?_⟩
  rw [output_eq, output_eq, mixMap_apply, h]

lemma trace_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d)))
    (X : Mat (Reg 1 d 1)) : (output 1 1 N X).trace = X.trace := by
  rw [output_eq, trace_ge, kraus_trace hN, trace_fe]

lemma rate_bound (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (m : ℕ) (eps : ℝ) (he1 : eps < 1) :
    blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps ≤
      ENNReal.ofReal (-Real.logb 2 (1 - eps)) / ((1 * (m + 1) : ℕ) : ℝ≥0∞) := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  obtain ⟨Phi, hPhi, hout⟩ := sim_output N hN hu X.1 X.2.1.1
  unfold testingBits
  refine iSup_le fun T => ?_
  have hmem : copies (m + 1) (output 1 1 N X.1) ∈
      {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output 1 1 Phi X.1)} := ⟨Phi, hPhi, by rw [hout]⟩
  have h1 := T.2.2 _ hmem
  have htr : (copies (m + 1) (output 1 1 N X.1)).trace = 1 := by
    rw [trace_copies, trace_output N hN, X.2.1.2, one_pow]
  have hp : 1 - eps ≤ effectProb T.1 (copies (m + 1) (output 1 1 N X.1)) := by
    unfold effectProb at h1 ⊢
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at h1
    simp only [Complex.one_re] at h1
    linarith
  rw [if_neg (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) (by linarith) hp)

lemma liminf_zero (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (eps : ℝ) (he1 : eps < 1) :
    liminf (fun m => blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps) atTop = 0 := by
  refine le_antisymm ?_ (zero_le)
  set C := ENNReal.ofReal (-Real.logb 2 (1 - eps))
  have ht : Tendsto (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top) (a := C)
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    simp [div_eq_mul_inv]
  calc _ ≤ liminf (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun m => rate_bound N hN hu m eps he1)
    _ = 0 := ht.liminf_eq

theorem main (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1) :
    blockExponent 1 (MU d) N 1 .unrestricted = 0 := by
  unfold blockExponent operational
  have : NeBot (𝓝[Set.Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot one_pos
  rw [liminf_congr (eventually_nhdsWithin_of_forall fun eps he =>
    liminf_zero N hN hu eps he.2 : ∀ᶠ eps in 𝓝[Set.Ioo (0:ℝ) 1] 0, _ = (fun _ => (0:ℝ≥0∞)) eps)]
  exact liminf_const 0

end X4P60

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} (hd : 3 ≤ d) (N : Maps d d) (hN : IsChannel N)
    (hu : N 1 = 1) (hn : N ∉ MU d) : blockExponent 1 (MU d) N 1 .unrestricted = 0 := by
  convert X4P60.main N hN (by convert hu)

end
