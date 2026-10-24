-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.mu_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:32:24.672654+00:00
-- url     : https://prove2.me/submissions/c6bafedf-0304-4cd8-a707-78ff4ed888c2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

-- ===== P60A =====

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

-- ===== P60B =====

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

-- ===== P60C =====

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


end

-- ===== P60D =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- mixed-unitary map over an arbitrary finite index. -/
def mixI {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ) : Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixI_apply {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (X : Mat (Fin d)) :
    mixI c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixI_mem {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∑ σ, c σ = 1) : mixI c U ∈ MU d := by
  set e := (Fintype.equivFin ι).symm
  refine ⟨?_, Fintype.card ι, c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card ι,
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixI_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixI_apply, ← Equiv.sum_comp e]
    rfl

/-! Depolarizing channel on qutrits as a unitary mixture. -/

def sgn (b : Bool) : ℂ := if b then -1 else 1

def signD (b : Bool × Bool × Bool) : Mat (Fin 3) :=
  Matrix.diagonal ![sgn b.1, sgn b.2.1, sgn b.2.2]

def rotP (a : Fin 3) : Mat (Fin 3) := ((finRotate 3) ^ (a : ℕ)).permMatrix ℂ

lemma signD_mem (b : Bool × Bool × Bool) : signD b ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, signD,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> cases b.1 <;> cases b.2.1 <;> cases b.2.2 <;> simp [sgn]

lemma sign_twirl (M : Mat (Fin 3)) :
    ∑ b, signD b * M * (signD b)ᴴ = (8 : ℂ) • Matrix.diagonal (fun i => M i i) := by
  ext i j
  simp only [Matrix.sum_apply, signD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Fintype.sum_bool]
  fin_cases i <;> fin_cases j <;> simp [sgn] <;> ring

lemma rot_sum (m : Fin 3 → ℂ) (i : Fin 3) : ∑ a : Fin 3, m (((finRotate 3) ^ (a : ℕ)) i) = ∑ j, m j := by
  have h1 : (finRotate 3) 0 = 1 := rfl
  have h2 : (finRotate 3) 1 = 2 := rfl
  have h3 : (finRotate 3) 2 = 0 := rfl
  fin_cases i <;> simp [Fin.sum_univ_three, pow_succ, Equiv.Perm.mul_apply, h1, h2, h3] <;> ring

lemma depol (M : Mat (Fin 3)) :
    ∑ p : Fin 3 × (Bool × Bool × Bool),
      (rotP p.1 * signD p.2) * M * (rotP p.1 * signD p.2)ᴴ = (8 * M.trace) • (1 : Mat (Fin 3)) := by
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin 3, ∑ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
      (8 : ℂ) • Matrix.diagonal ((fun i => M i i) ∘ ((finRotate 3 ^ (a : ℕ)))) := by
    intro a
    have : ∀ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
        rotP a * (signD b * M * (signD b)ᴴ) * (rotP a)ᴴ := fun b => by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sign_twirl, Matrix.mul_smul, Matrix.smul_mul, rotP,
      perm_conj_diag]
  simp only [this]
  rw [← Finset.smul_sum]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, Function.comp_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · subst h; rw [rot_sum (fun i => M i i) i, Matrix.trace]; simp
  · simp

end X4P60

end

-- ===== P60Q =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Tensor powers of matrices (`kp`) and the block-output of a mixed-unitary channel. -/

/-- tensor product of a family of square matrices. -/
def kp {n : ℕ} {I : Type*} (U : Fin n → Matrix I I ℂ) : Matrix (Fin n → I) (Fin n → I) ℂ :=
  Matrix.of fun y x => ∏ l, U l (y l) (x l)

section kp
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

lemma kp_apply (U : Fin n → Matrix I I ℂ) (y x : Fin n → I) : kp U y x = ∏ l, U l (y l) (x l) := rfl

lemma kp_mul (U V : Fin n → Matrix I I ℂ) : kp U * kp V = kp (fun l => U l * V l) := by
  ext y x
  simp only [kp, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma kp_conjTranspose (U : Fin n → Matrix I I ℂ) : (kp U)ᴴ = kp (fun l => (U l)ᴴ) := by
  ext y x
  simp [kp, Matrix.conjTranspose_apply]

lemma kp_one : kp (fun _ : Fin n => (1 : Matrix I I ℂ)) = 1 := by
  ext y x
  simp only [kp, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma kp_unitary (U : Fin n → Matrix I I ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup I ℂ) :
    kp U ∈ Matrix.unitaryGroup (Fin n → I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kp_conjTranspose, kp_mul]
  have : ∀ l, (U l)ᴴ * U l = 1 := fun l => by
    have := (Matrix.mem_unitaryGroup_iff'.1 (hU l)); rwa [Matrix.star_eq_conjTranspose] at this
  simp only [this]
  exact kp_one

lemma kp_smul (c : Fin n → ℂ) (U : Fin n → Matrix I I ℂ) :
    kp (fun l => c l • U l) = (∏ l, c l) • kp U := by
  ext y x
  simp [kp, Finset.prod_mul_distrib]

lemma kp_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Fin n → ι → Matrix I I ℂ) :
    kp (fun l => ∑ j, f l j) = ∑ L : Fin n → ι, kp (fun l => f l (L l)) := by
  ext y x
  simp only [kp, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma copies_eq_kp (m : ℕ) (X : Matrix I I ℂ) : copies m X = kp (fun _ => X) := rfl

/-- tensor powers of a unitary mixture form a unitary mixture. -/
lemma copies_mix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (W : ι → Matrix I I ℂ)
    (Y : Matrix I I ℂ) (m : ℕ) :
    copies m (∑ j, (c j : ℂ) • (W j * Y * (W j)ᴴ)) =
      ∑ L : Fin m → ι, ((∏ l, c (L l) : ℝ) : ℂ) •
        (kp (fun l => W (L l)) * copies m Y * (kp (fun l => W (L l)))ᴴ) := by
  rw [copies_eq_kp, kp_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [kp_smul, copies_eq_kp, kp_conjTranspose, kp_mul, kp_mul]
  push_cast
  rfl

end kp

/-- matrices on the reference ⊗ system register acting trivially on the reference. -/
def lift {r d k : ℕ} (A : Mat (Fin k → Fin d)) : Mat (Reg r d k) :=
  Matrix.of fun p q => if p.1 = q.1 then A p.2 q.2 else 0

section lift
variable {r d k : ℕ}

lemma lift_apply (A : Mat (Fin k → Fin d)) (p q : Reg r d k) :
    (lift A : Mat (Reg r d k)) p q = if p.1 = q.1 then A p.2 q.2 else 0 := rfl

lemma lift_mul (A B : Mat (Fin k → Fin d)) :
    (lift A : Mat (Reg r d k)) * lift B = lift (A * B) := by
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type, lift_apply]
  simp only [lift_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single q.1 (fun x hx => by simp [hx])]
  simp only [if_true]
  by_cases h : p.1 = q.1
  · simp only [h, if_true]; rw [Matrix.mul_apply]
  · simp [h]

lemma lift_conjTranspose (A : Mat (Fin k → Fin d)) :
    (lift A : Mat (Reg r d k))ᴴ = lift Aᴴ := by
  ext p q
  rw [Matrix.conjTranspose_apply, lift_apply, lift_apply]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

lemma lift_one : (lift (1 : Mat (Fin k → Fin d)) : Mat (Reg r d k)) = 1 := by
  ext p q
  rw [lift_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

lemma lift_unitary (A : Mat (Fin k → Fin d)) (hA : A ∈ Matrix.unitaryGroup _ ℂ) :
    (lift A : Mat (Reg r d k)) ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, lift_conjTranspose, lift_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA
  rw [hA, lift_one]

end lift

section outmix
variable {r d k q : ℕ}

lemma conj_single_apply (U : Mat (Fin d)) (a b c c' : Fin d) :
    ((U * Matrix.single a b (1 : ℂ) * Uᴴ : Mat (Fin d))) c c' = U c a * conj (U c' b) := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

lemma lift_conj_apply (A : Mat (Fin k → Fin d)) (X : Mat (Reg r d k)) (p p' : Reg r d k) :
    (((lift A : Mat (Reg r d k)) * X * (lift A)ᴴ : Mat (Reg r d k))) p p' =
      ∑ x, ∑ x', A p.2 x * X (p.1, x) (p'.1, x') * conj (A p'.2 x') := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, lift_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hs : ∀ (x : Fin k → Fin r) (y : Fin k → Fin d), star (if p'.1 = x then A p'.2 y else 0) =
      if p'.1 = x then star (A p'.2 y) else 0 := by intros; split_ifs <;> simp
  simp only [hs, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  rfl

/-- the block output of a mixed-unitary channel. -/
lemma out_mix (Q : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hQ : ∀ X, Q X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    (X : Mat (Reg r d k)) :
    output r k Q X = ∑ J : Fin k → Fin q, ((∏ i, w (J i) : ℝ) : ℂ) •
      (lift (kp (fun i => (U (J i) : Mat (Fin d)))) * X *
        (lift (kp (fun i => (U (J i) : Mat (Fin d)))))ᴴ) := by
  ext p p'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, lift_conj_apply, kp_apply]
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, hQ, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, conj_single_apply]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  rw [map_prod, Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end outmix

end X4P60

end

-- ===== P60R =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Heisenberg-picture tests, composition of block outputs, closure of MU. -/

section heis
variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι]

lemma effectProb_heis (c : ι → ℝ) (V : ι → Matrix I I ℂ) (T Z : Matrix I I ℂ) :
    effectProb (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)) Z =
      effectProb T (∑ L, (c L : ℂ) • (V L * Z * (V L)ᴴ)) := by
  simp only [effectProb, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul]
  congr 1
  refine Finset.sum_congr rfl fun L _ => ?_
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc]

lemma heis_sub (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc1 : ∑ L, c L = 1) (T : Matrix I I ℂ) :
    1 - ∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L) = ∑ L, (c L : ℂ) • ((V L)ᴴ * (1 - T) * V L) := by
  have h1 : (1 : Matrix I I ℂ) = ∑ L, (c L : ℂ) • ((V L)ᴴ * 1 * V L) := by
    simp only [Matrix.mul_one, hV, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, hc1]; simp
  conv_lhs => rw [h1]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [← smul_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma heis_psd (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hc0 : ∀ L, 0 ≤ c L) {T : Matrix I I ℂ}
    (hT : T.PosSemidef) : (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun L _ => ?_
  have := hT.conjTranspose_mul_mul_same (V L)
  exact this.smul (by exact_mod_cast hc0 L)

lemma heis_effect (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc0 : ∀ L, 0 ≤ c L) (hc1 : ∑ L, c L = 1) {T : Matrix I I ℂ} (hT : IsEffect T) :
    IsEffect (∑ L, (c L : ℂ) • ((V L)ᴴ * T * V L)) :=
  ⟨heis_psd c V hc0 hT.1, by rw [heis_sub c V hV hc1]; exact heis_psd c V hc0 hT.2⟩

lemma mix_density (c : ι → ℝ) (V : ι → Matrix I I ℂ) (hV : ∀ L, (V L)ᴴ * V L = 1)
    (hc0 : ∀ L, 0 ≤ c L) (hc1 : ∑ L, c L = 1) {X : Matrix I I ℂ} (hX : IsDensityMatrix X) :
    IsDensityMatrix (∑ L, (c L : ℂ) • (V L * X * (V L)ᴴ)) := by
  refine ⟨Matrix.posSemidef_sum _ fun L _ => (hX.1.mul_mul_conjTranspose_same (V L)).smul
    (by exact_mod_cast hc0 L), ?_⟩
  rw [Matrix.trace_sum]
  have : ∀ L, ((c L : ℂ) • (V L * X * (V L)ᴴ)).trace = (c L : ℂ) * X.trace := fun L => by
    rw [Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, smul_eq_mul]
  simp only [this, hX.2, mul_one]
  exact_mod_cast hc1

end heis

/-! composition of block outputs -/

lemma clm_entry {a b : ℕ} (Ψ : Maps a b) (A : Mat (Fin a)) (y y' : Fin b) :
    Ψ A y y' = ∑ z, ∑ z', A z z' * Ψ (Matrix.single z z' 1) y y' := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [show Matrix.single z z' (A z z') = A z z' • Matrix.single z z' (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

lemma pi_comp {d k : ℕ} (Ψ Φ : Maps d d) (Y : Mat (Fin k → Fin d)) :
    piSuperop (fun _ : Fin k => ((Ψ.comp Φ : Maps d d) : Superop (Fin d) (Fin d))) Y =
      piSuperop (fun _ : Fin k => (Ψ : Superop (Fin d) (Fin d)))
        (piSuperop (fun _ : Fin k => (Φ : Superop (Fin d) (Fin d))) Y) := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, ContinuousLinearMap.comp_apply]
  simp only [clm_entry Ψ (Φ _)]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => enter [2, z]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => enter [2, z]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

lemma out_comp {r d k : ℕ} (Ψ Φ : Maps d d) (X : Mat (Reg r d k)) :
    output r k (Ψ.comp Φ) X = output r k Ψ (output r k Φ X) := by
  ext p q
  simp only [output, idTensorSuperop, Matrix.of_apply]
  rw [pi_comp]
  rfl

/-! closure of MU under composition -/

lemma mu_comp {d : ℕ} {P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d) : Q.comp P ∈ MU d := by
  obtain ⟨-, q1, w1, U1, h01, h11, e1⟩ := hP
  obtain ⟨-, q2, w2, U2, h02, h12, e2⟩ := hQ
  have : Q.comp P = mixI (fun o : Fin q2 × Fin q1 => w2 o.1 * w1 o.2) (fun o => U2 o.1 * U1 o.2) := by
    ext1 X
    rw [ContinuousLinearMap.comp_apply, mixI_apply, e2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [e1]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast; rfl
  rw [this]
  refine mixI_mem _ _ (fun o => mul_nonneg (h02 _) (h01 _)) ?_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, h11, mul_one, h12]

end X4P60

end

-- ===== P60S =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! MU preprocessing preserves each admissible probe class. -/

section adm
variable {r d k q : ℕ}

lemma sum_prod_w {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (h : ∑ j, w j = 1) :
    ∑ J : Fin n → ι, ∏ i, w (J i) = 1 := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [h]

lemma prod_w_nonneg {n : ℕ} (w : Fin q → ℝ) (h : ∀ j, 0 ≤ w j) (J : Fin n → Fin q) :
    0 ≤ ∏ i, w (J i) := Finset.prod_nonneg fun i _ => h _

/-- `1 ⊗ U` on reference × system. -/
def L1 (U : Mat (Fin d)) : Mat (Fin r × Fin d) := (1 : Mat (Fin r)) ⊗ₖ U

lemma L1_unitary (U : Mat (Fin d)) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (L1 U : Mat (Fin r × Fin d))ᴴ * L1 U = 1 := by
  rw [L1, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
    Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  rw [hU, Matrix.one_kronecker_one]

def EE : Reg r d k ≃ (Fin k → Fin r × Fin d) := (Equiv.arrowProdEquivProdArrow _ _ _).symm

lemma pp_eq (τ : Fin k → Mat (Fin r × Fin d)) :
    productProbe τ = (kp τ).submatrix EE EE := rfl

lemma lift_eq (V : Fin k → Mat (Fin d)) :
    (lift (kp V) : Mat (Reg r d k)) = (kp (fun i => (L1 (V i) : Mat (Fin r × Fin d)))).submatrix EE EE := by
  ext p p'
  rw [lift_apply, Matrix.submatrix_apply, kp_apply, kp_apply]
  simp only [L1, Matrix.kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  by_cases h : p.1 = p'.1
  · simp [EE, h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, p.1 i ≠ p'.1 i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    simp [EE, hi]

lemma prod_out (P : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hP : ∀ X, P X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    (τ : Fin k → Mat (Fin r × Fin d)) :
    output r k P (productProbe τ) = productProbe (fun i => ∑ j, (w j : ℂ) •
      (L1 (U j : Mat (Fin d)) * τ i * (L1 (U j : Mat (Fin d)))ᴴ)) := by
  rw [out_mix P w U hP, pp_eq, pp_eq, kp_sum]
  simp only [lift_eq, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, kp_conjTranspose,
    kp_mul, kp_smul]
  ext p p'
  simp only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.smul_apply, Complex.ofReal_prod]

lemma out_lin (P : Maps d d) (w : Fin q → ℝ) (U : Fin q → Matrix.unitaryGroup (Fin d) ℂ)
    (hP : ∀ X, P X = ∑ j, (w j : ℂ) • ((U j : Mat (Fin d)) * X * (U j : Mat (Fin d))ᴴ))
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (X : ι → Mat (Reg r d k)) :
    output r k P (∑ j, a j • X j) = ∑ j, a j • output r k P (X j) := by
  simp only [out_mix P w U hP, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J _ => ?_
  rw [mul_comm]

lemma W_unitary (V : Fin k → Matrix.unitaryGroup (Fin d) ℂ) :
    (lift (kp fun i => (V i : Mat (Fin d))) : Mat (Reg r d k))ᴴ *
      lift (kp fun i => (V i : Mat (Fin d))) = 1 := by
  have := lift_unitary (r := r) _ (kp_unitary (fun i => (V i : Mat (Fin d))) (fun i => (V i).2))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
  exact this

lemma adm_out {P : Maps d d} (hP : P ∈ MU d) {c : Correlation} {X : Mat (Reg r d k)}
    (hX : X ∈ admissible r d k c) : output r k P X ∈ admissible r d k c := by
  obtain ⟨-, q, w, U, h0, h1, e⟩ := hP
  have hden : ∀ {Y : Mat (Reg r d k)}, IsDensityMatrix Y → IsDensityMatrix (output r k P Y) := by
    intro Y hY
    rw [out_mix P w U e]
    exact mix_density _ _ (fun J => W_unitary _) (fun J => prod_w_nonneg w h0 J)
      (sum_prod_w w h1) hY
  have hτ : ∀ {τ : Mat (Fin r × Fin d)}, IsDensityMatrix τ → IsDensityMatrix (∑ j, (w j : ℂ) •
      (L1 (U j : Mat (Fin d)) * τ * (L1 (U j : Mat (Fin d)))ᴴ)) := fun hτ =>
    mix_density _ _ (fun j => L1_unitary _ (U j).2) h0 h1 hτ
  refine ⟨hden hX.1, ?_⟩
  obtain ⟨-, hX2⟩ := hX
  cases c with
  | unrestricted => trivial
  | product =>
    obtain ⟨τ, hτd, rfl⟩ := hX2
    exact ⟨_, fun i => hτ (hτd i), prod_out P w U e τ⟩
  | separable =>
    obtain ⟨q', w', τ, h0', h1', hτd, rfl⟩ := hX2
    refine ⟨q', w', _, h0', h1', fun j i => hτ (hτd j i), ?_⟩
    rw [out_lin P w U e]
    simp only [prod_out P w U e]

end adm

end X4P60

end

-- ===== P60TSol =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section mono
variable {d : ℕ}

/-- the tests of the `M` problem pull back to tests of the `N` problem. -/
lemma testing_mono {r k m : ℕ} {N M P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d)
    (hM : M = Q.comp (N.comp P)) (X : Mat (Reg r d k)) (eps : ℝ) :
    testingBits {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output r k Phi X)}
        (copies (m + 1) (output r k M X)) eps ≤
      testingBits {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output r k Phi (output r k P X))}
        (copies (m + 1) (output r k N (output r k P X))) eps := by
  obtain ⟨-, q, w, U, h0, h1, e⟩ := id hQ
  set W : (Fin k → Fin q) → Mat (Reg r d k) := fun J => lift (kp fun i => (U (J i) : Mat (Fin d)))
  set cJ : (Fin k → Fin q) → ℝ := fun J => ∏ i, w (J i)
  set cc : (Fin (m + 1) → Fin k → Fin q) → ℝ := fun L => ∏ l, cJ (L l)
  set VV : (Fin (m + 1) → Fin k → Fin q) → Mat (Fin (m + 1) → Reg r d k) :=
    fun L => kp fun l => W (L l)
  have hVV : ∀ L, (VV L)ᴴ * VV L = 1 := fun L => by
    simp only [VV, kp_conjTranspose, kp_mul, W, W_unitary, kp_one]
  have hcc0 : ∀ L, 0 ≤ cc L := fun L => Finset.prod_nonneg fun l _ => prod_w_nonneg w h0 _
  have hcc1 : ∑ L, cc L = 1 := sum_prod_w cJ (sum_prod_w w h1)
  have hQY : ∀ Y : Mat (Reg r d k), copies (m + 1) (output r k Q Y) =
      ∑ L, (cc L : ℂ) • (VV L * copies (m + 1) Y * (VV L)ᴴ) := fun Y => by
    rw [out_mix Q w U e, copies_mix]
  have key : ∀ (T : Mat (Fin (m + 1) → Reg r d k)) (Y : Mat (Reg r d k)),
      effectProb (∑ L, (cc L : ℂ) • ((VV L)ᴴ * T * VV L)) (copies (m + 1) Y) =
        effectProb T (copies (m + 1) (output r k Q Y)) := fun T Y => by
    rw [effectProb_heis, hQY]
  unfold testingBits
  refine iSup_le fun T => ?_
  obtain ⟨T, hTe, hT1⟩ := T
  refine le_iSup_of_le ⟨∑ L, (cc L : ℂ) • ((VV L)ᴴ * T * VV L),
    heis_effect cc VV hVV hcc0 hcc1 hTe, ?_⟩ (le_of_eq ?_)
  · rintro ρ ⟨Phi, hPhi, rfl⟩
    rw [heis_sub cc VV hVV hcc1, key]
    exact hT1 _ ⟨Q.comp (Phi.comp P), mu_comp (mu_comp hP hPhi) hQ, by rw [out_comp, out_comp]⟩
  · simp only
    rw [key, hM, out_comp, out_comp]

lemma rate_mono {r k : ℕ} {N M P Q : Maps d d} (hP : P ∈ MU d) (hQ : Q ∈ MU d)
    (hM : M = Q.comp (N.comp P)) (c : Correlation) (m : ℕ) (eps : ℝ) :
    blockRate r (MU d) M k (admissible r d k c) m eps ≤
      blockRate r (MU d) N k (admissible r d k c) m eps := by
  unfold blockRate
  refine ENNReal.div_le_div_right ?_ _
  refine iSup_le fun X => ?_
  exact le_iSup_of_le ⟨output r k P X.1, adm_out hP X.2⟩ (testing_mono hP hQ hM X.1 eps)

lemma exp_mono {r k : ℕ} {N M : Maps d d} (h : MUConvertible N M) (c : Correlation) :
    blockExponent r (MU d) M k c ≤ blockExponent r (MU d) N k c := by
  obtain ⟨P, hP, Q, hQ, hM⟩ := h
  have hM' : M = Q.comp (N.comp P) := by ext1 X; exact hM X
  unfold blockExponent operational
  refine liminf_le_liminf (Eventually.of_forall fun eps => ?_)
  exact liminf_le_liminf (Eventually.of_forall fun m => rate_mono hP hQ hM' c m eps)

lemma ad_mem (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ P ∈ MU d, ∀ X, P X = (U : Mat (Fin d)) * X * (U : Mat (Fin d))ᴴ :=
  ⟨mixI (fun _ : Unit => 1) (fun _ => U), mixI_mem _ _ (fun _ => zero_le_one) (by simp),
    fun X => by simp [mixI_apply]⟩

lemma conv_of_ue {N M : Maps d d} (h : UnitaryEquivalent N M) :
    MUConvertible N M ∧ MUConvertible M N := by
  obtain ⟨U, V, hUV⟩ := h
  obtain ⟨P, hP, eP⟩ := ad_mem U
  obtain ⟨Q, hQ, eQ⟩ := ad_mem V
  obtain ⟨P', hP', eP'⟩ := ad_mem (star U)
  obtain ⟨Q', hQ', eQ'⟩ := ad_mem (star V)
  have hU : (U : Mat (Fin d)) * (U : Mat (Fin d))ᴴ = 1 := by
    have := Unitary.coe_mul_star_self U; exact this
  have hV : (V : Mat (Fin d))ᴴ * (V : Mat (Fin d)) = 1 := by
    have := Unitary.coe_star_mul_self V; exact this
  refine ⟨⟨P, hP, Q, hQ, fun X => by rw [hUV X, eP, eQ]⟩, ⟨P', hP', Q', hQ', fun X => ?_⟩⟩
  rw [eP', eQ', Unitary.coe_star, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have : M ((U : Mat (Fin d))ᴴ * X * (U : Mat (Fin d))) = (V : Mat (Fin d)) * N X * (V : Mat (Fin d))ᴴ := by
    rw [hUV]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hV,
    Matrix.mul_one]

end mono

end X4P60

section
open X4P60 QAlgorithms QAlgorithms.Papers.Independent.Information100.P60
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} (hd : 0 < d) (N M : Maps d d)
    (hN : IsChannel N) (hM : IsChannel M) (h : MUConvertible N M) (k : ℕ) (hk : 0 < k) :
    ∀ r ∈ ({1, d} : Set ℕ), ∀ c,
      blockExponent r (MU d) M k c ≤ blockExponent r (MU d) N k c ∧
      (UnitaryEquivalent N M → blockExponent r (MU d) M k c = blockExponent r (MU d) N k c) := by
  intro r _ c
  refine ⟨exp_mono h c, fun hue => ?_⟩
  exact le_antisymm (exp_mono h c) (exp_mono (conv_of_ue hue).2 c)

end

end
