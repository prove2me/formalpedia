-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.pure_pair_simulation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:10:11.166643+00:00
-- url     : https://prove2.me/submissions/64c9b345-2dff-4716-b2b2-12377577f7d2

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

-- ===== P60K =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Vectors in ℂ³: inner product, conjugated cross product, rank-one projectors. -/

abbrev V3 := Fin 3 → ℂ

def ip (x y : V3) : ℂ := ∑ i, conj (x i) * y i

/-- conjugated cross product: orthogonal to both arguments. -/
def cc (a b : V3) : V3 :=
  ![conj (a 1 * b 2 - a 2 * b 1), conj (a 2 * b 0 - a 0 * b 2), conj (a 0 * b 1 - a 1 * b 0)]

def pd (v : V3) : Mat (Fin 3) := Matrix.of fun i j => v i * conj (v j)

lemma ip_conj (x y : V3) : ip y x = conj (ip x y) := by
  simp only [ip, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma ip_cc_left (a b : V3) : ip (cc a b) a = 0 := by
  simp only [ip, cc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Complex.conj_conj, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma ip_cc_right (a b : V3) : ip (cc a b) b = 0 := by
  simp only [ip, cc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Complex.conj_conj, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma ip_cc_cc (a b c d : V3) :
    ip (cc a b) (cc c d) = ip c a * ip d b - ip d a * ip c b := by
  simp only [ip, cc, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Complex.conj_conj, Matrix.head_cons, Matrix.tail_cons, map_sub, map_mul]
  ring

lemma ip_add_right (x y z : V3) : ip x (y + z) = ip x y + ip x z := by
  simp only [ip, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma ip_add_left (x y z : V3) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma ip_smul_right (x y : V3) (c : ℂ) : ip x (c • y) = c * ip x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ip_smul_left (x y : V3) (c : ℂ) : ip (c • x) y = conj c * ip x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ip_sub_right (x y z : V3) : ip x (y - z) = ip x y - ip x z := by
  simp only [ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma ip_sub_left (x y z : V3) : ip (x - y) z = ip x z - ip y z := by
  simp only [ip, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

lemma ip_self_re (x : V3) : ip x x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  simp only [ip, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]

lemma ip_self_eq_zero {x : V3} (h : ip x x = 0) : x = 0 := by
  rw [ip_self_re, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)] at h
  funext i
  exact Complex.normSq_eq_zero.1 (h i (Finset.mem_univ _))

lemma normSq_ip_le {x y : V3} (hx : ip x x = 1) (hy : ip y y = 1) :
    Complex.normSq (ip x y) ≤ 1 ∧ (Complex.normSq (ip x y) = 1 → pd y = pd x) := by
  set c := ip x y
  have key : ip (y - c • x) (y - c • x) = 1 - (Complex.normSq c : ℂ) := by
    rw [ip_sub_left, ip_sub_right, ip_sub_right, ip_smul_right, ip_smul_right, ip_smul_left,
      ip_smul_left, hx, hy, ip_conj x y, Complex.normSq_eq_conj_mul_self]
    ring
  have hre := congrArg Complex.re key
  rw [ip_self_re, Complex.ofReal_re] at hre
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
  refine ⟨?_, fun h1 => ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg ((y - c • x) i))
    linarith
  · rw [h1, Complex.ofReal_one, sub_self] at key
    have h0 := ip_self_eq_zero key
    have hy' : y = c • x := by rw [← sub_eq_zero]; exact h0
    rw [hy']
    ext i j
    simp only [pd, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    have : c * conj c = 1 := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, h1, Complex.ofReal_one]
    linear_combination (x i * conj (x j)) * this

lemma pd_smul (v : V3) {c : ℂ} (hc : conj c * c = 1) : pd (c • v) = pd v := by
  ext i j
  simp only [pd, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (v i * conj (v j)) * hc

lemma pd_conj_mul (U : Mat (Fin 3)) (v : V3) : U * pd v * Uᴴ = pd (U *ᵥ v) := by
  ext i j
  simp only [pd, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, map_add, map_mul, Complex.star_def]
  ring

/-- two-dimensional unitary rotation of a pair of vectors. -/
lemma pd_pair (ξ η : V3) {p q : ℂ} (h : p * conj p + q * conj q = 1) :
    pd (p • ξ + q • η) + pd ((-conj q) • ξ + conj p • η) = pd ξ + pd η := by
  ext i j
  simp only [pd, Matrix.add_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, map_neg, Complex.conj_conj]
  linear_combination (ξ i * conj (ξ j) + η i * conj (η j)) * h

/-- orthonormal triples resolve the identity. -/
lemma pd_three (e : Fin 3 → V3) (he : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0) :
    pd (e 0) + pd (e 1) + pd (e 2) = 1 := by
  set E : Mat (Fin 3) := Matrix.of fun r k => e k r
  have h1 : Eᴴ * E = 1 := by
    ext k l
    simp only [E, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← he k l, ip]
    rfl
  have h2 : E * Eᴴ = 1 := mul_eq_one_comm.1 h1
  rw [← h2]
  ext i j
  simp only [E, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply,
    pd, Fin.sum_univ_three, Complex.star_def]

/-- the orthonormal frame matrix of an orthonormal pair completed by the cross product. -/
def frame (e0 e1 : V3) : Mat (Fin 3) := Matrix.of fun r k => (![e0, e1, cc e0 e1] k) r

lemma frame_on {e0 e1 : V3} (h00 : ip e0 e0 = 1) (h11 : ip e1 e1 = 1) (h01 : ip e0 e1 = 0) :
    ∀ k l, ip (![e0, e1, cc e0 e1] k) (![e0, e1, cc e0 e1] l) = if k = l then 1 else 0 := by
  have h10 : ip e1 e0 = 0 := by rw [ip_conj, h01, map_zero]
  have h20 := ip_cc_left e0 e1
  have h21 := ip_cc_right e0 e1
  have h02 : ip e0 (cc e0 e1) = 0 := by rw [ip_conj, h20, map_zero]
  have h12 : ip e1 (cc e0 e1) = 0 := by rw [ip_conj, h21, map_zero]
  have h22 : ip (cc e0 e1) (cc e0 e1) = 1 := by rw [ip_cc_cc, h00, h11, h01, h10]; ring
  intro k l
  fin_cases k <;> fin_cases l <;> simp [h00, h11, h01, h10, h20, h21, h02, h12, h22]

lemma frame_hh {e0 e1 : V3} (h00 : ip e0 e0 = 1) (h11 : ip e1 e1 = 1) (h01 : ip e0 e1 = 0) :
    (frame e0 e1)ᴴ * frame e0 e1 = 1 := by
  ext k l
  simp only [frame, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← frame_on h00 h11 h01 k l, ip]
  rfl

lemma frame_mulVec (e0 e1 : V3) (v : Fin 3 → ℂ) :
    frame e0 e1 *ᵥ v = v 0 • e0 + v 1 • e1 + v 2 • cc e0 e1 := by
  funext r
  simp [frame, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

lemma frameH_mulVec {e0 e1 : V3} (h00 : ip e0 e0 = 1) (h11 : ip e1 e1 = 1) (h01 : ip e0 e1 = 0)
    (v : V3) : (frame e0 e1)ᴴ *ᵥ v = ![ip e0 v, ip e1 v, ip (cc e0 e1) v] := by
  funext k
  fin_cases k <;> simp [frame, Matrix.mulVec, dotProduct, ip, Fin.sum_univ_three]

/-- unitary mapping one orthonormal pair to another. -/
lemma exists_unitary_on {e0 e1 f0 f1 : V3} (h00 : ip e0 e0 = 1) (h11 : ip e1 e1 = 1)
    (h01 : ip e0 e1 = 0) (g00 : ip f0 f0 = 1) (g11 : ip f1 f1 = 1) (g01 : ip f0 f1 = 0) :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ, U *ᵥ e0 = f0 ∧ U *ᵥ e1 = f1 := by
  refine ⟨frame f0 f1 * (frame e0 e1)ᴴ, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (frame f0 f1)ᴴ,
      frame_hh g00 g11 g01, Matrix.one_mul]
    exact mul_eq_one_comm.1 (frame_hh h00 h11 h01)
  · have h02 : ip e0 (cc e0 e1) = 0 := by rw [ip_conj, ip_cc_left, map_zero]
    rw [← Matrix.mulVec_mulVec, frameH_mulVec h00 h11 h01, frame_mulVec, h00, ip_cc_left]
    have h10 : ip e1 e0 = 0 := by rw [ip_conj, h01, map_zero]
    simp [h10]
  · have h10 : ip e1 e0 = 0 := by rw [ip_conj, h01, map_zero]
    have h12 : ip e1 (cc e0 e1) = 0 := by rw [ip_conj, ip_cc_right, map_zero]
    rw [← Matrix.mulVec_mulVec, frameH_mulVec h00 h11 h01, frame_mulVec, h11, ip_cc_right]
    simp [h01]

/-- Gram-matrix criterion (Chefles–Jozsa–Winter) for two unit vectors with overlap of modulus < 1. -/
lemma exists_unitary_gram {x1 x2 y1 y2 : V3} (hx1 : ip x1 x1 = 1) (hx2 : ip x2 x2 = 1)
    (hy1 : ip y1 y1 = 1) (hy2 : ip y2 y2 = 1) (hg : ip x1 x2 = ip y1 y2)
    (hlt : Complex.normSq (ip x1 x2) < 1) :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ, U *ᵥ x1 = y1 ∧ U *ᵥ x2 = y2 := by
  set a := ip x1 x2
  set b : ℝ := Real.sqrt (1 - Complex.normSq a)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hbb : ((b : ℂ)) ^ 2 = 1 - conj a * a := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← Complex.normSq_eq_conj_mul_self]
    push_cast; ring
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  set e1 := ((b : ℂ)⁻¹) • (x2 - a • x1)
  set f1 := ((b : ℂ)⁻¹) • (y2 - a • y1)
  have hna : (Complex.normSq a : ℂ) = conj a * a := by rw [Complex.normSq_eq_conj_mul_self]
  have h01 : ip x1 e1 = 0 := by
    rw [ip_smul_right, ip_sub_right, ip_smul_right, hx1]; ring
  have g01 : ip y1 f1 = 0 := by
    rw [ip_smul_right, ip_sub_right, ip_smul_right, hy1, ← hg]; ring
  have hbc : conj ((b : ℂ)⁻¹) = (b : ℂ)⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
  have h11 : ip e1 e1 = 1 := by
    rw [ip_smul_left, ip_smul_right, ip_sub_left, ip_sub_right, ip_sub_right, ip_smul_left,
      ip_smul_right, ip_smul_left, ip_smul_right, hx1, hx2, ip_conj x1 x2, hbc]
    field_simp
    linear_combination (-1 : ℂ) * hbb
  have g11 : ip f1 f1 = 1 := by
    rw [ip_smul_left, ip_smul_right, ip_sub_left, ip_sub_right, ip_sub_right, ip_smul_left,
      ip_smul_right, ip_smul_left, ip_smul_right, hy1, hy2, ip_conj y1 y2, ← hg, hbc]
    field_simp
    linear_combination (-1 : ℂ) * hbb
  obtain ⟨U, hU, h1, h2⟩ := exists_unitary_on hx1 h11 h01 hy1 g11 g01
  refine ⟨U, hU, h1, ?_⟩
  have ex : x2 = a • x1 + (b : ℂ) • e1 := by
    simp only [e1, smul_smul, mul_inv_cancel₀ hb0, one_smul]; abel
  have ey : y2 = a • y1 + (b : ℂ) • f1 := by
    simp only [f1, smul_smul, mul_inv_cancel₀ hb0, one_smul]; abel
  rw [ex, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, ← ey]

end X4P60

end

-- ===== P60L =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Structure of O(3)-covariant qutrit channels: `N X = a X + b Xᵀ + q tr(X) 1`. -/

lemma cov_entry {N : Maps 3 3} (hc : OrthogonalCovariant N) (O : Matrix (Fin 3) (Fin 3) ℝ)
    (h1 : O.transpose * O = 1) (h2 : O * O.transpose = 1) (X : Mat (Fin 3)) (k l : Fin 3) :
    N (O.map (fun x => (x : ℂ)) * X * (O.map (fun x => (x : ℂ))).transpose) k l =
      (O.map (fun x => (x : ℂ)) * N X * (O.map (fun x => (x : ℂ))).transpose) k l := by
  have := hc O h1 h2 X
  exact congrArg (fun M => M k l) this

def sgnM (s : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal s

lemma sign_rel {N : Maps 3 3} (hc : OrthogonalCovariant N) (s : Fin 3 → ℝ)
    (hs : ∀ i, s i * s i = 1) (i j k l : Fin 3) :
    ((s i * s j : ℝ) : ℂ) * N (Matrix.single i j 1) k l =
      ((s k * s l : ℝ) : ℂ) * N (Matrix.single i j 1) k l := by
  have h1 : (sgnM s).transpose * sgnM s = 1 := by
    rw [sgnM, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact hs i
  have h2 : sgnM s * (sgnM s).transpose = 1 := by
    rw [sgnM, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact hs i
  have e := cov_entry hc (sgnM s) h1 h2 (Matrix.single i j 1) k l
  have hm : (sgnM s).map (fun x => (x : ℂ)) = Matrix.diagonal (fun i => (s i : ℂ)) := by
    rw [sgnM, Matrix.diagonal_map (by simp)]
  rw [hm, Matrix.diagonal_transpose] at e
  have hE : Matrix.diagonal (fun i => (s i : ℂ)) * Matrix.single i j 1 *
      Matrix.diagonal (fun i => (s i : ℂ)) = ((s i * s j : ℝ) : ℂ) • Matrix.single i j 1 := by
    ext x y
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.smul_apply,
      smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; push_cast; ring
    · simp
  rw [hE, map_smul, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul] at e
  rw [e]; push_cast; ring

def permO (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun k x => if σ k = x then 1 else 0

lemma perm_rel {N : Maps 3 3} (hc : OrthogonalCovariant N) (σ : Equiv.Perm (Fin 3))
    (a b k l : Fin 3) :
    N (Matrix.single (σ.symm a) (σ.symm b) 1) k l = N (Matrix.single a b 1) (σ k) (σ l) := by
  have h1 : (permO σ).transpose * permO σ = 1 := by
    ext x y
    simp only [permO, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Equiv.sum_comp σ (fun z => (if z = x then (1 : ℝ) else 0) * (if z = y then 1 else 0))]
    simp [eq_comm]
  have h2 : permO σ * (permO σ).transpose = 1 := by
    ext x y
    simp only [permO, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    simp [σ.injective.eq_iff]
  have e := cov_entry hc (permO σ) h1 h2 (Matrix.single a b 1) k l
  have hm : (permO σ).map (fun x => (x : ℂ)) = Matrix.of fun k x => if σ k = x then (1 : ℂ) else 0 := by
    ext k x; simp [permO, apply_ite]
  have hE : (Matrix.of fun k x => if σ k = x then (1 : ℂ) else 0) * Matrix.single a b 1 *
      (Matrix.of fun k x => if σ k = x then (1 : ℂ) else 0).transpose =
      Matrix.single (σ.symm a) (σ.symm b) 1 := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.single_apply]
    simp [Equiv.eq_symm_apply, ite_and, eq_comm]
    split_ifs <;> rfl
  rw [hm, hE] at e
  rw [e]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  simp

def rotO : Matrix (Fin 3) (Fin 3) ℝ := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1]

lemma rot_rel {N : Maps 3 3} (hc : OrthogonalCovariant N) :
    (9/25 : ℂ) * N (Matrix.single 0 0 1) 0 1 + (12/25 : ℂ) * N (Matrix.single 0 1 1) 0 1 +
      (12/25 : ℂ) * N (Matrix.single 1 0 1) 0 1 + (16/25 : ℂ) * N (Matrix.single 1 1 1) 0 1 =
    ∑ x, ∑ y, ((rotO 0 x * rotO 1 y : ℝ) : ℂ) * N (Matrix.single 0 0 1) x y := by
  have h1 : rotO.transpose * rotO = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotO, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have h2 : rotO * rotO.transpose = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotO, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have e := cov_entry hc rotO h1 h2 (Matrix.single 0 0 1) 0 1
  have hE : rotO.map (fun x => (x : ℂ)) * Matrix.single 0 0 1 * (rotO.map (fun x => (x : ℂ))).transpose
      = (9/25 : ℂ) • Matrix.single 0 0 1 + (12/25 : ℂ) • Matrix.single 0 1 1 +
        (12/25 : ℂ) • Matrix.single 1 0 1 + (16/25 : ℂ) • Matrix.single 1 1 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rotO, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] <;> norm_num
  rw [hE] at e
  simp only [map_add, map_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e
  rw [e]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  push_cast; ring

lemma sgn_zero {N : Maps 3 3} (hc : OrthogonalCovariant N) (s : Fin 3 → ℝ)
    (hs : ∀ i, s i * s i = 1) {i j k l : Fin 3} (hne : s i * s j ≠ s k * s l) :
    N (Matrix.single i j 1) k l = 0 := by
  have h := sign_rel hc s hs i j k l
  have h' : (((s i * s j : ℝ) : ℂ) - ((s k * s l : ℝ) : ℂ)) * N (Matrix.single i j 1) k l = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

lemma inv_rel {N : Maps 3 3} (hc : OrthogonalCovariant N) (τ : Equiv.Perm (Fin 3))
    (i j k l : Fin 3) :
    N (Matrix.single i j 1) k l = N (Matrix.single (τ i) (τ j) 1) (τ k) (τ l) := by
  have := perm_rel hc τ (τ i) (τ j) k l
  simpa using this

def cf (a b q : ℂ) (i j k l : Fin 3) : ℂ :=
  (if i = k ∧ j = l then a else 0) + (if j = k ∧ i = l then b else 0) +
    (if i = j ∧ k = l then q else 0)

lemma cf_inv (a b q : ℂ) (τ : Equiv.Perm (Fin 3)) (i j k l : Fin 3) :
    cf a b q (τ i) (τ j) (τ k) (τ l) = cf a b q i j k l := by
  simp [cf, τ.injective.eq_iff]

def s0 : Fin 3 → ℝ := fun i => if i = 0 then -1 else 1
def s1 : Fin 3 → ℝ := fun i => if i = 1 then -1 else 1
def s2 : Fin 3 → ℝ := fun i => if i = 2 then -1 else 1
lemma hs0 : ∀ i, s0 i * s0 i = 1 := by intro i; simp only [s0]; split_ifs <;> norm_num
lemma hs1 : ∀ i, s1 i * s1 i = 1 := by intro i; simp only [s1]; split_ifs <;> norm_num
lemma hs2 : ∀ i, s2 i * s2 i = 1 := by intro i; simp only [s2]; split_ifs <;> norm_num

lemma perm_exists : ∀ i j : Fin 3, i ≠ j → ∃ τ : Equiv.Perm (Fin 3), τ i = 0 ∧ τ j = 1 := by
  decide

def cA (N : Maps 3 3) : ℂ := N (Matrix.single 0 1 1) 0 1
def cB (N : Maps 3 3) : ℂ := N (Matrix.single 0 1 1) 1 0
def cQ (N : Maps 3 3) : ℂ := N (Matrix.single 0 0 1) 1 1

lemma cform {N : Maps 3 3} (hc : OrthogonalCovariant N) (i j k l : Fin 3) :
    N (Matrix.single i j 1) k l = cf (cA N) (cB N) (cQ N) i j k l := by
  have z := fun s hs {i j k l : Fin 3} (hne : s i * s j ≠ s k * s l) => sgn_zero hc s hs hne
  have hb : N (Matrix.single 1 0 1) 0 1 = cB N := by
    rw [inv_rel hc (Equiv.swap 0 1)]; simp [cB]
  have hq : N (Matrix.single 0 0 1) 2 2 = cQ N := by
    rw [inv_rel hc (Equiv.swap 1 2), show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]; simp [cQ]
  have hr := rot_rel hc
  have z1 : N (Matrix.single 0 0 1) 0 1 = 0 := z s0 hs0 (by norm_num [s0, Fin.ext_iff])
  have z2 : N (Matrix.single 1 1 1) 0 1 = 0 := z s0 hs0 (by norm_num [s0, Fin.ext_iff])
  have z3 : N (Matrix.single 0 0 1) 1 0 = 0 := z s0 hs0 (by norm_num [s0, Fin.ext_iff])
  have z4 : N (Matrix.single 0 0 1) 0 2 = 0 := z s0 hs0 (by norm_num [s0, Fin.ext_iff])
  have z5 : N (Matrix.single 0 0 1) 2 0 = 0 := z s0 hs0 (by norm_num [s0, Fin.ext_iff])
  have z6 : N (Matrix.single 0 0 1) 1 2 = 0 := z s1 hs1 (by norm_num [s1, Fin.ext_iff])
  have z7 : N (Matrix.single 0 0 1) 2 1 = 0 := z s1 hs1 (by norm_num [s1, Fin.ext_iff])
  have c00 : ∀ k l, N (Matrix.single 0 0 1) k l = cf (cA N) (cB N) (cQ N) 0 0 k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [cf, z1, z3, z4, z5, z6, z7, hq, cQ]
    · simp [rotO, Fin.sum_univ_three, z1, z2, z3, hb] at hr
      simp only [cA, cB, cQ] at hr ⊢
      linear_combination (-25/12 : ℂ) * hr
  have c01 : ∀ k l, N (Matrix.single 0 1 1) k l = cf (cA N) (cB N) (cQ N) 0 1 k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp only [cf] <;> norm_num [Fin.ext_iff]
    all_goals first
      | rfl
      | (refine z s0 hs0 ?_; norm_num [s0, Fin.ext_iff]; done)
      | (refine z s1 hs1 ?_; norm_num [s1, Fin.ext_iff]; done)
      | (refine z s2 hs2 ?_; norm_num [s2, Fin.ext_iff]; done)
  by_cases hij : i = j
  · subst hij
    rw [inv_rel hc (Equiv.swap i 0), ← cf_inv _ _ _ (Equiv.swap i 0) i i k l]
    simp only [Equiv.swap_apply_left]
    exact c00 _ _
  · obtain ⟨τ, h1, h2⟩ := perm_exists i j hij
    rw [inv_rel hc τ, ← cf_inv _ _ _ τ i j k l, h1, h2]
    exact c01 _ _

lemma classify {N : Maps 3 3} (hc : OrthogonalCovariant N) (X : Mat (Fin 3)) :
    N X = cA N • X + cB N • X.transpose + (cQ N * X.trace) • (1 : Mat (Fin 3)) := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  conv_lhs => rw [hX]
  ext k l
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, cform hc]
  simp only [cf, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.one_apply,
    Matrix.trace, Matrix.diag, smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    ite_and]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h
    simp only [Fin.sum_univ_three]
    fin_cases k <;> simp <;> ring
  · simp; ring

end X4P60

end

-- ===== P60M =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Complete positivity constraints for O(3)-covariant channels. -/

lemma choi_nonneg {N : Maps 3 3} (hN : IsChannel (N : Superop (Fin 3) (Fin 3)))
    (v : Fin 3 → Fin 3 → ℂ) :
    0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, conj (v i k) * v j l * N (Matrix.single i j 1) k l := by
  obtain ⟨m, E, -, hE⟩ := hN
  have hent : ∀ i j k l, N (Matrix.single i j 1) k l = ∑ t, E t k i * conj (E t l j) := by
    intro i j k l
    rw [hE, krausApply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Matrix.mul_apply]
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  set w : Fin m → ℂ := fun t => ∑ j, ∑ l, v j l * conj (E t l j)
  have : ∑ i, ∑ j, ∑ k, ∑ l, conj (v i k) * v j l * N (Matrix.single i j 1) k l =
      ∑ t, conj (w t) * w t := by
    simp only [hent, w, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => enter [2, i, 2, j, 2, k]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => enter [2, i]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this]
  refine Finset.sum_nonneg fun t _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast Complex.normSq_nonneg _

lemma choi_cf {N : Maps 3 3} (hc : OrthogonalCovariant N)
    (v : Fin 3 → Fin 3 → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, conj (v i k) * v j l * N (Matrix.single i j 1) k l =
      cA N * ((∑ i, conj (v i i)) * ∑ j, v j j) + cB N * ∑ i, ∑ j, conj (v i j) * v j i +
        cQ N * ∑ i, ∑ k, conj (v i k) * v i k := by
  simp only [cform hc, cf, Fin.sum_univ_three]
  simp
  ring

lemma constraints {N : Maps 3 3} (hN : IsChannel (N : Superop (Fin 3) (Fin 3)))
    (hc : OrthogonalCovariant N) :
    ∃ α β γ : ℝ, cA N = α ∧ cB N = β ∧ cQ N = γ ∧ β ≤ γ ∧ -β ≤ γ ∧ 0 ≤ 3 * α + β + γ ∧
      0 ≤ α + β + γ ∧ α + β + 3 * γ = 1 := by
  have P := fun v => (choi_cf hc v) ▸ choi_nonneg hN v
  have p1 := P (fun i k => if i = 0 ∧ k = 1 then 1 else if i = 1 ∧ k = 0 then -1 else 0)
  have p2 := P (fun i k => if i = 0 ∧ k = 1 then 1 else if i = 1 ∧ k = 0 then 1 else 0)
  have p3 := P (fun i k => if i = k then 1 else 0)
  have p4 := P (fun i k => if i = 0 ∧ k = 0 then 1 else 0)
  have p5 := P (fun i k => if i = 0 ∧ k = 1 then 1 else 0)
  simp only [Fin.sum_univ_three] at p1 p2 p3 p4 p5
  norm_num [Fin.ext_iff] at p1 p2 p3 p4 p5
  have ht := kraus_trace hN (Matrix.single 0 0 1)
  rw [classify hc] at ht
  simp [Matrix.trace, Fin.sum_univ_three] at ht
  rw [Complex.nonneg_iff] at p2 p4 p5
  rw [Complex.le_def] at p1 p3
  simp at p1 p2 p3 p4 p5
  have hq : cQ N = ((cQ N).re : ℂ) := by apply Complex.ext <;> simp [p5.2]
  have hb : cB N = ((cB N).re : ℂ) := by apply Complex.ext <;> simp; linarith [p2.2, p5.2]
  have ha : cA N = ((cA N).re : ℂ) := by apply Complex.ext <;> simp; linarith [p4.2, p2.2, p5.2]
  refine ⟨(cA N).re, (cB N).re, (cQ N).re, ha, hb, hq, p1.1, by linarith [p2.1], by linarith [p3.1],
    p4.1, ?_⟩
  have := congrArg Complex.re ht
  simp at this
  linarith

end X4P60

end

-- ===== P60N =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Pair simulation of the Werner–Holevo-type output `1 - |χ⟩⟨χ|` (Appendix A, Step 1). -/

lemma ip_comb (p q p' q' : ℂ) (x y z w : V3) :
    ip (p • x + q • y) (p' • z + q' • w) =
      conj p * p' * ip x z + conj p * q' * ip x w + conj q * p' * ip y z + conj q * q' * ip y w := by
  rw [ip_add_left, ip_add_right, ip_add_right, ip_smul_left, ip_smul_left, ip_smul_left,
    ip_smul_left, ip_smul_right, ip_smul_right, ip_smul_right, ip_smul_right]
  ring

lemma ip_star (x y : V3) : ip (star x) (star y) = ip y x := by
  simp only [ip, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- unit phase normalising a nonzero overlap. -/
lemma phase_facts (α : ℂ) :
    ∃ ω : ℂ, conj ω * ω = 1 ∧ α = ω * (‖α‖ : ℂ) := by
  by_cases h : α = 0
  · exact ⟨1, by simp, by simp [h]⟩
  · have hm : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
    refine ⟨α / (‖α‖ : ℂ), ?_, by field_simp⟩
    rw [map_div₀, Complex.conj_ofReal]
    field_simp
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; ring

lemma cd_facts {m : ℝ} (h0 : 0 ≤ m) (h1 : m < 1) :
    ∃ c d : ℝ, c * c + d * d = 1 ∧ c * d * (1 + m) = m := by
  set s := m / (1 + m)
  have hs0 : 0 ≤ s := div_nonneg h0 (by linarith)
  have hs : 4 * s * s ≤ 1 := by
    have : s ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith
  set t := Real.sqrt (1 - 4 * s * s)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = 1 - 4 * s * s := Real.mul_self_sqrt (by linarith)
  have ht1 : t ≤ 1 := by nlinarith
  set x := (1 + t) / 2
  refine ⟨Real.sqrt x, Real.sqrt (1 - x), ?_, ?_⟩
  · rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by simp only [x]; linarith)]; ring
  · rw [← Real.sqrt_mul (by positivity)]
    have : x * (1 - x) = s * s := by simp only [x]; nlinarith
    rw [this, Real.sqrt_mul_self hs0]
    simp only [s]; field_simp

lemma wh_sim {ψ1 ψ2 χ1 χ2 : V3} (h1 : ip ψ1 ψ1 = 1) (h2 : ip ψ2 ψ2 = 1)
    (hlt : Complex.normSq (ip ψ1 ψ2) < 1) (k1 : ip χ1 χ1 = 1) (k2 : ip χ2 χ2 = 1)
    (hk : ip χ2 χ1 = ip ψ1 ψ2) :
    ∃ U1 ∈ Matrix.unitaryGroup (Fin 3) ℂ, ∃ U2 ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      pd (U1 *ᵥ ψ1) + pd (U2 *ᵥ ψ1) = 1 - pd χ1 ∧ pd (U1 *ᵥ ψ2) + pd (U2 *ᵥ ψ2) = 1 - pd χ2 := by
  set α := ip ψ1 ψ2 with hαdef
  have hα1 : ip χ1 χ2 = conj α := by rw [ip_conj, hk]
  have hna : Complex.normSq α = conj α * α := Complex.normSq_eq_conj_mul_self
  set n := cc χ1 χ2
  have hn : ip n n = 1 - conj α * α := by rw [ip_cc_cc, k1, k2, hk, hα1]; ring
  set r : ℝ := Real.sqrt (1 - Complex.normSq α)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hrr : (r : ℂ) ^ 2 = 1 - conj α * α := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith), ← hna]; push_cast; ring
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set η := ((r : ℂ)⁻¹) • n
  have hηη : ip η η = 1 := by
    rw [ip_smul_left, ip_smul_right, hn, map_inv₀, Complex.conj_ofReal, ← hrr]
    field_simp
  have hη1 : ip η χ1 = 0 := by rw [ip_smul_left, ip_cc_left]; simp
  have hη2 : ip η χ2 = 0 := by rw [ip_smul_left, ip_cc_right]; simp
  have h1η : ip χ1 η = 0 := by rw [ip_conj, hη1, map_zero]
  have h2η : ip χ2 η = 0 := by rw [ip_conj, hη2, map_zero]
  set ξ1 := cc η χ1
  set ξ2 := cc η χ2
  have hξ1 : ip ξ1 ξ1 = 1 := by rw [ip_cc_cc, hηη, k1, hη1, h1η]; ring
  have hξ2 : ip ξ2 ξ2 = 1 := by rw [ip_cc_cc, hηη, k2, hη2, h2η]; ring
  have hξη1 : ip ξ1 η = 0 := ip_cc_left _ _
  have hξη2 : ip ξ2 η = 0 := ip_cc_left _ _
  have hηξ1 : ip η ξ1 = 0 := by rw [ip_conj, hξη1, map_zero]
  have hηξ2 : ip η ξ2 = 0 := by rw [ip_conj, hξη2, map_zero]
  have hξχ1 : ip ξ1 χ1 = 0 := ip_cc_right _ _
  have hξχ2 : ip ξ2 χ2 = 0 := ip_cc_right _ _
  have hχξ1 : ip χ1 ξ1 = 0 := by rw [ip_conj, hξχ1, map_zero]
  have hχξ2 : ip χ2 ξ2 = 0 := by rw [ip_conj, hξχ2, map_zero]
  have hξ12 : ip ξ1 ξ2 = α := by rw [ip_cc_cc, hηη, hk, h2η, hη1]; ring
  have comp1 : pd ξ1 + pd η + pd χ1 = 1 := by
    have := pd_three ![ξ1, η, χ1] (by
      intro k l; fin_cases k <;> fin_cases l <;> simp [hξ1, hηη, k1, hξη1, hηξ1, hξχ1, hχξ1, hη1, h1η])
    simpa using this
  have comp2 : pd ξ2 + pd η + pd χ2 = 1 := by
    have := pd_three ![ξ2, η, χ2] (by
      intro k l; fin_cases k <;> fin_cases l <;> simp [hξ2, hηη, k2, hξη2, hηξ2, hξχ2, hχξ2, hη2, h2η])
    simpa using this
  obtain ⟨ω, hω, hαω⟩ := phase_facts α
  have hm1 : ‖α‖ < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hlt
    nlinarith [norm_nonneg α]
  obtain ⟨c, d, hcd1, hcd⟩ := cd_facts (norm_nonneg α) hm1
  have hcdC : (c : ℂ) * c + (d : ℂ) * d = 1 := by exact_mod_cast hcd1
  have hcdα : (c : ℂ) * d * (1 + (‖α‖ : ℂ)) = ‖α‖ := by exact_mod_cast hcd
  have hωc : ω * conj ω = 1 := by rw [mul_comm]; exact hω
  set u11 := (c : ℂ) • ξ1 + (d : ℂ) • η
  set u12 := (-(d : ℂ)) • ξ1 + (c : ℂ) • η
  set u21 := (d : ℂ) • ξ2 + ((c : ℂ) * ω) • η
  set u22 := (-((c : ℂ) * conj ω)) • ξ2 + (d : ℂ) • η
  have cr : ∀ x : ℝ, conj (x : ℂ) = x := fun x => Complex.conj_ofReal x
  have g11 : ip u11 u11 = 1 := by
    rw [ip_comb, hξ1, hηη, hξη1, hηξ1, cr, cr]; linear_combination hcdC
  have g12 : ip u12 u12 = 1 := by
    rw [ip_comb, hξ1, hηη, hξη1, hηξ1, map_neg, cr, cr]; linear_combination hcdC
  have g21 : ip u21 u21 = 1 := by
    rw [ip_comb, hξ2, hηη, hξη2, hηξ2, map_mul, cr, cr]; linear_combination hcdC + (c : ℂ) * c * hω
  have g22 : ip (ω • u22) (ω • u22) = 1 := by
    rw [ip_smul_left, ip_smul_right, ip_comb, hξ2, hηη, hξη2, hηξ2, map_neg, map_mul, cr, cr,
      Complex.conj_conj]
    linear_combination (c * c * conj ω * ω + d * d) * hω + hcdC + (c : ℂ) * c * hω
  have x11 : ip ψ1 ψ2 = ip u11 u21 := by
    rw [ip_comb, hξ12, hξη1, hηξ2, hηη, cr, cr]
    linear_combination (1 - (c : ℂ) * d) * hαω - ω * hcdα
  have x22 : ip ψ1 ψ2 = ip u12 (ω • u22) := by
    rw [ip_smul_right, ip_comb, hξ12, hξη1, hηξ2, hηη, map_neg, cr, cr]
    linear_combination (1 - (c : ℂ) * d) * hαω - ω * hcdα - ((c : ℂ) * d * α) * hωc
  obtain ⟨U1, hU1, e11, e21⟩ := exists_unitary_gram h1 h2 g11 g21 x11 hlt
  obtain ⟨U2, hU2, e12, e22⟩ := exists_unitary_gram h1 h2 g12 g22 x22 hlt
  refine ⟨U1, hU1, U2, hU2, ?_, ?_⟩
  · have hp : pd u11 + pd u12 = pd ξ1 + pd η := by
      have hp := pd_pair ξ1 η (p := (c : ℂ)) (q := (d : ℂ)) (by rw [cr, cr]; exact hcdC)
      rw [cr, cr] at hp; exact hp
    rw [e11, e12, hp, ← comp1]; abel
  · rw [e21, e22, pd_smul _ hω]
    have := pd_pair ξ2 η (p := d) (q := (c : ℂ) * ω) (by
      rw [map_mul, cr, cr]; linear_combination hcdC + (c : ℂ) * c * hωc)
    rw [map_mul, cr, cr] at this
    have hp : pd u21 + pd u22 = pd ξ2 + pd η := this
    rw [hp, ← comp2]; abel

end X4P60

end

-- ===== P60O =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

/-! Assembly: simulating `ρ ↦ α ρ + β ρ̄ + γ 1` on a pair of pure states by one MU channel. -/

lemma phase2 (α : ℂ) : ∃ θ : ℂ, conj θ * θ = 1 ∧ θ * conj α = α := by
  obtain ⟨ω, hω, hαω⟩ := phase_facts α
  refine ⟨ω * ω, ?_, ?_⟩
  · rw [map_mul]; linear_combination (conj ω * ω + 1) * hω
  · rw [hαω, map_mul, Complex.conj_ofReal]
    linear_combination (ω * (‖α‖ : ℂ)) * hω

lemma tsim {ψ1 ψ2 : V3} (h1 : ip ψ1 ψ1 = 1) (h2 : ip ψ2 ψ2 = 1)
    (hlt : Complex.normSq (ip ψ1 ψ2) < 1) :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      pd (U *ᵥ ψ1) = pd (star ψ1) ∧ pd (U *ᵥ ψ2) = pd (star ψ2) := by
  obtain ⟨θ, hθ, hθα⟩ := phase2 (ip ψ1 ψ2)
  have hθ' : conj (conj θ) * conj θ = 1 := by rw [Complex.conj_conj, mul_comm]; exact hθ
  have s1 : ip (star ψ1) (star ψ1) = 1 := by rw [ip_star, h1]
  have s2 : ip (star ψ2) (star ψ2) = 1 := by rw [ip_star, h2]
  have y1 : ip (conj θ • star ψ1) (conj θ • star ψ1) = 1 := by
    rw [ip_smul_left, ip_smul_right, s1]; linear_combination hθ'
  have g : ip ψ1 ψ2 = ip (conj θ • star ψ1) (star ψ2) := by
    rw [ip_smul_left, Complex.conj_conj, ip_star, ip_conj ψ1 ψ2, hθα]
  obtain ⟨U, hU, e1, e2⟩ := exists_unitary_gram h1 h2 y1 s2 g hlt
  exact ⟨U, hU, by rw [e1, pd_smul _ hθ'], by rw [e2]⟩

abbrev Ix := Fin 6 ⊕ (Fin 3 × (Bool × Bool × Bool))

def depU (p : Fin 3 × (Bool × Bool × Bool)) : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨rotP p.1 * signD p.2, Submonoid.mul_mem _ (perm_unitary _) (signD_mem _)⟩

lemma trace_pd (v : V3) : (pd v).trace = ip v v := by
  simp only [Matrix.trace, Matrix.diag, pd, Matrix.of_apply, ip]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma core {ψ1 ψ2 : V3} (h1 : ip ψ1 ψ1 = 1) (h2 : ip ψ2 ψ2 = 1)
    (hlt : Complex.normSq (ip ψ1 ψ2) < 1) (α β γ : ℝ) (c1 : β ≤ γ) (c2 : -β ≤ γ)
    (c3 : 0 ≤ 3 * α + β + γ) (c4 : 0 ≤ α + β + γ) (c5 : α + β + 3 * γ = 1) :
    ∃ Φ ∈ MU 3, ∀ v ∈ ({ψ1, ψ2} : Set V3),
      Φ (pd v) = (α : ℂ) • pd v + (β : ℂ) • pd (star v) + (γ : ℂ) • 1 := by
  obtain ⟨UT, hUT, t1, t2⟩ := tsim h1 h2 hlt
  have s1 : ip (star ψ1) (star ψ1) = 1 := by rw [ip_star, h1]
  have s2 : ip (star ψ2) (star ψ2) = 1 := by rw [ip_star, h2]
  obtain ⟨U1, hU1, U2, hU2, w1, w2⟩ := wh_sim h1 h2 hlt s1 s2 (by rw [ip_star])
  obtain ⟨θ, hθ, hθα⟩ := phase2 (ip ψ1 ψ2)
  have y1 : ip (θ • ψ1) (θ • ψ1) = 1 := by rw [ip_smul_left, ip_smul_right, h1]; linear_combination hθ
  obtain ⟨V1, hV1, V2, hV2, v1, v2⟩ := wh_sim h1 h2 hlt y1 h2
    (by rw [ip_smul_right, ip_conj ψ1 ψ2, hθα])
  rw [pd_smul _ hθ] at v1
  set A := max α 0
  set A' := max (-α) 0
  set B := max β 0
  set B' := max (-β) 0
  set D := γ - A' - B'
  have hA : A - A' = α := by simp only [A, A']; rcases le_total 0 α with h | h <;> simp [h]
  have hB : B - B' = β := by simp only [B, B']; rcases le_total 0 β with h | h <;> simp [h]
  have hA0 : 0 ≤ A := le_max_right _ _
  have hA0' : 0 ≤ A' := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB0' : 0 ≤ B' := le_max_right _ _
  have hD : 0 ≤ D := by
    simp only [D, A', B']
    rcases le_total 0 α with h | h <;> rcases le_total 0 β with h' | h' <;>
      simp [h, h'] <;> linarith
  let w6 : Fin 6 → ℝ := ![A, B, B', B', A', A']
  let c : Ix → ℝ := Sum.elim w6 (fun _ => D / 8)
  let U6 : Fin 6 → Matrix.unitaryGroup (Fin 3) ℂ :=
    ![1, ⟨UT, hUT⟩, ⟨U1, hU1⟩, ⟨U2, hU2⟩, ⟨V1, hV1⟩, ⟨V2, hV2⟩]
  let U : Ix → Matrix.unitaryGroup (Fin 3) ℂ := Sum.elim U6 depU
  have hc0 : ∀ o, 0 ≤ c o := by
    rintro (o | o)
    · fin_cases o <;> simp [c, w6, hA0, hA0', hB0, hB0']
    · simp only [c, Sum.elim_inr]; positivity
  have hc1 : ∑ o, c o = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fin.sum_univ_six,
      w6, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    simp
    linarith
  refine ⟨mixI c U, mixI_mem c U hc0 hc1, ?_⟩
  have key : ∀ v : V3, ip v v = 1 → pd (UT *ᵥ v) = pd (star v) →
      pd (U1 *ᵥ v) + pd (U2 *ᵥ v) = 1 - pd (star v) →
      pd (V1 *ᵥ v) + pd (V2 *ᵥ v) = 1 - pd v →
      mixI c U (pd v) = (α : ℂ) • pd v + (β : ℂ) • pd (star v) + (γ : ℂ) • 1 := by
    intro v hv eT eW eW'
    rw [mixI_apply, Fintype.sum_sum_type]
    simp only [c, U, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_six]
    have q0 : w6 0 = A := rfl
    have q1 : w6 1 = B := rfl
    have q2 : w6 2 = B' := rfl
    have q3 : w6 3 = B' := rfl
    have q4 : w6 4 = A' := rfl
    have q5 : w6 5 = A' := rfl
    have r0 : ((U6 0 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = 1 := rfl
    have r1 : ((U6 1 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = UT := rfl
    have r2 : ((U6 2 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = U1 := rfl
    have r3 : ((U6 3 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = U2 := rfl
    have r4 : ((U6 4 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = V1 := rfl
    have r5 : ((U6 5 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat (Fin 3)) = V2 := rfl
    rw [q0, q1, q2, q3, q4, q5, r0, r1, r2, r3, r4, r5]
    rw [← Finset.smul_sum]
    have hd := depol (pd v)
    simp only [depU]
    rw [hd, trace_pd, hv]
    simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, pd_conj_mul]
    rw [eT]
    have eW2 : pd (U2 *ᵥ v) = 1 - pd (star v) - pd (U1 *ᵥ v) := by rw [← eW]; abel
    have eW2' : pd (V2 *ᵥ v) = 1 - pd v - pd (V1 *ᵥ v) := by rw [← eW']; abel
    rw [eW2, eW2']
    have hAc : (α : ℂ) = A - A' := by rw [← hA]; push_cast; ring
    have hBc : (β : ℂ) = B - B' := by rw [← hB]; push_cast; ring
    have hDc : (D : ℂ) = γ - A' - B' := by simp only [D]; push_cast; ring
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-pd v i j) * hAc - (pd (star v) i j) * hBc + (1 : Mat (Fin 3)) i j * hDc
  intro v hv
  rcases hv with rfl | rfl
  · exact key _ h1 t1 w1 v1
  · exact key _ h2 t2 w2 v2

end X4P60

end

-- ===== P60PSol =====

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma pd_transpose (v : V3) : (pd v).transpose = pd (star v) := by
  ext i j; simp [pd, mul_comm]

lemma N_pd {N : Maps 3 3} (hc : OrthogonalCovariant N) (v : V3) (hv : ip v v = 1) :
    N (pd v) = cA N • pd v + cB N • pd (star v) + cQ N • 1 := by
  rw [classify hc, pd_transpose, trace_pd, hv, mul_one]

lemma unit_of_norm (psi : EuclideanSpace ℂ (Fin 3)) (hp : ‖psi‖ = 1) :
    ip (fun i => psi i) (fun i => psi i) = 1 := by
  rw [ip_self_re]
  have h := EuclideanSpace.norm_eq psi
  rw [hp] at h
  have h2 : ∑ i, ‖psi i‖ ^ 2 = 1 := by
    have := congrArg (· ^ 2) h
    simp only [one_pow] at this
    rw [this, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Complex.normSq_eq_norm_sq, h2, Complex.ofReal_one]

lemma exists_far (v : V3) (hv : ip v v = 1) :
    ∃ e : V3, ip e e = 1 ∧ Complex.normSq (ip v e) < 1 := by
  have hs : ∑ i, Complex.normSq (v i) = 1 := by
    have := hv; rw [ip_self_re] at this; exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have : ∀ j, 1 ≤ Complex.normSq (v j) := by
    intro j
    have h := hcon (Pi.single j 1) (by simp [ip, Pi.single_apply])
    simpa [ip, Pi.single_apply] using h
  rw [Fin.sum_univ_three] at hs
  linarith [this 0, this 1, this 2]

end X4P60

section
open X4P60 QAlgorithms QAlgorithms.Papers.Independent.Information100.P60
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (N : Maps 3 3) (hN : IsChannel N) (hc : OrthogonalCovariant N)
    (psi phi : EuclideanSpace ℂ (Fin 3)) (hp : ‖psi‖ = 1) (hq : ‖phi‖ = 1) :
    ∃ Phi ∈ MU 3, Phi (pureDensity psi) = N (pureDensity psi) ∧
      Phi (pureDensity phi) = N (pureDensity phi) := by
  obtain ⟨α, β, γ, ha, hb, hg, c1, c2, c3, c4, c5⟩ := constraints hN hc
  set v : V3 := fun i => psi i
  set w : V3 := fun i => phi i
  have hv : ip v v = 1 := unit_of_norm psi hp
  have hw : ip w w = 1 := unit_of_norm phi hq
  have e1 : pureDensity psi = pd v := rfl
  have e2 : pureDensity phi = pd w := rfl
  rw [e1, e2, N_pd hc v hv, N_pd hc w hw, ha, hb, hg]
  obtain ⟨hle, heq⟩ := normSq_ip_le hv hw
  rcases hle.lt_or_eq with hlt | h1
  · obtain ⟨Φ, hΦ, hΦv⟩ := core hv hw hlt α β γ c1 c2 c3 c4 c5
    exact ⟨Φ, hΦ, hΦv v (by simp), hΦv w (by simp)⟩
  · have hpw := heq h1
    obtain ⟨e, he, hlt⟩ := exists_far v hv
    obtain ⟨Φ, hΦ, hΦv⟩ := core hv he hlt α β γ c1 c2 c3 c4 c5
    have hst : pd (star w) = pd (star v) := by rw [← pd_transpose, hpw, pd_transpose]
    refine ⟨Φ, hΦ, hΦv v (by simp), ?_⟩
    rw [hpw, hst]
    exact hΦv v (by simp)

end

end
