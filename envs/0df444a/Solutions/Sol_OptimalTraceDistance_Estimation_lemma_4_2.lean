-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T06:01:21.818795+00:00
-- url     : https://prove2.me/submissions/3e9504de-8156-4cfe-864e-2068e6534d9d

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OTDLem42
open Matrix OptimalTraceDistance.Estimation Equiv

/-- Trace functional of a permutation against a family of matrices. -/
def T {ι : Type*} [Fintype ι] (n : ℕ) (M : Fin n → Matrix ι ι ℂ) (σ : Perm (Fin n)) : ℂ :=
  ∑ x : Fin n → ι, ∏ i, M (σ i) (x (σ i)) (x i)

lemma sum_cons {ι : Type*} [Fintype ι] {n : ℕ} (f : (Fin (n+1) → ι) → ℂ) :
    ∑ x, f x = ∑ x0 : ι, ∑ x' : Fin n → ι, f (Fin.cons x0 x') := by
  rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma T_zero {ι : Type*} [Fintype ι] {n : ℕ} (M : Fin (n+1) → Matrix ι ι ℂ) (e : Perm (Fin n)) :
    T (n+1) M (Perm.decomposeFin.symm (0, e)) = (M 0).trace * T n (fun i => M i.succ) e := by
  unfold T
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Perm.decomposeFin_symm_apply_zero,
    Perm.decomposeFin_symm_apply_succ, swap_self, Equiv.refl_apply, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [Finset.mul_sum]
  rfl

lemma T_succ {ι : Type*} [Fintype ι] {n : ℕ} (M : Fin (n+1) → Matrix ι ι ℂ) (e : Perm (Fin n))
    (q : Fin n) :
    T (n+1) M (Perm.decomposeFin.symm (q.succ, e)) =
      T n (fun i => if i = q then M i.succ * M 0 else M i.succ) e := by
  unfold T
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Perm.decomposeFin_symm_apply_zero,
    Perm.decomposeFin_symm_apply_succ, Fin.cons_zero]
  set y0 := e.symm q with hy0
  have hswap : ∀ y : Fin n, swap 0 q.succ (e y).succ = if e y = q then 0 else (e y).succ := by
    intro y
    by_cases h : e y = q
    · rw [if_pos h, h, swap_apply_right]
    · rw [if_neg h, swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h' => h (Fin.succ_injective _ h'))]
  simp only [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  -- split off y0 on both sides
  have hsplit : ∀ (F : Fin n → ℂ), ∏ y, F y = F y0 * ∏ y ∈ Finset.univ.erase y0, F y := fun F =>
    (Finset.mul_prod_erase _ _ (Finset.mem_univ y0)).symm
  have hey0 : e y0 = q := by rw [hy0]; simp
  have hrest : ∀ x0 : ι, ∏ y ∈ Finset.univ.erase y0,
      M (if e y = q then 0 else (e y).succ) ((Fin.cons x0 x' : Fin (n+1) → ι) (if e y = q then 0 else (e y).succ))
        (x' y) =
      ∏ y ∈ Finset.univ.erase y0,
        (if e y = q then M (e y).succ * M 0 else M (e y).succ) (x' (e y)) (x' y) := by
    intro x0
    refine Finset.prod_congr rfl (fun y hy => ?_)
    have hne : e y ≠ q := by
      intro h; apply Finset.ne_of_mem_erase hy; rw [hy0, ← h]; simp
    simp only [if_neg hne, Fin.cons_succ]
  simp only [hsplit, hey0, if_true, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [hrest x0]; ring

variable {d : ℕ} in
lemma sum_normsq (y : Fin d → ℂ) : star y ⬝ᵥ y = ∑ i, ((‖y i‖^2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  show y i * (starRingEnd ℂ) (y i) = _
  rw [Complex.mul_conj', Complex.ofReal_pow]


variable {d : ℕ} in
lemma inner_eq (A : Mat d) (x : EuclideanSpace ℂ (Fin d)) :
    RCLike.re (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) x) =
      (star (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Pi.star_apply, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

variable {d : ℕ} in
lemma normsq_eq (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖^2 = (star (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

variable {d : ℕ} in
lemma quad_le_opNorm (A : Mat d) (x : Fin d → ℂ) :
    |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ opNorm A * (star x ⬝ᵥ x).re := by
  have := ContinuousLinearMap.rayleighQuotient_le_norm (Matrix.toEuclideanCLM (𝕜 := ℂ) A)
    (WithLp.toLp 2 x)
  simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] at this
  rw [inner_eq, normsq_eq] at this
  simp only [WithLp.ofLp_toLp] at this
  rcases eq_or_lt_of_le (show 0 ≤ (star x ⬝ᵥ x).re from by
      rw [sum_normsq]; simp only [Complex.re_sum, Complex.ofReal_re]; positivity) with h0 | hpos
  · have hx : x = 0 := by
      have := (h0.symm)
      rw [sum_normsq] at this
      simp only [Complex.re_sum, Complex.ofReal_re] at this
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖x i‖)).mp this
      funext i; have := h2 i (Finset.mem_univ i); simpa using this
    subst hx; simp
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at this
    exact this



section spectral
variable {d : ℕ} {A : Mat d} (hA : A.IsHermitian)
include hA

lemma U_mem : (hA.eigenvectorUnitary : Mat d) ∈ unitary (Mat d) := (hA.eigenvectorUnitary).2

lemma cfc_explicit (f : ℝ → ℝ) : cfc f A =
    (hA.eigenvectorUnitary : Mat d) * diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Mat d) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma trace_cfc (f : ℝ → ℝ) : (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_explicit hA, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (U_mem hA),
    Matrix.one_mul, trace_diagonal]

end spectral

lemma eig_le_opNorm {d : ℕ} {R : Mat d} (hH : R.IsHermitian) (i : Fin d) :
    hH.eigenvalues i ≤ opNorm R := by
  set v := hH.eigenvectorBasis i
  have hv := hH.mulVec_eigenvectorBasis i
  have h1 := quad_le_opNorm R (⇑v)
  have hn : (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ)).re = 1 := by
    have := normsq_eq v
    rw [hH.eigenvectorBasis.orthonormal.1 i] at this
    simpa using this.symm
  rw [hv, dotProduct_smul, hn, mul_one] at h1
  have : (hH.eigenvalues i • (star (⇑v) ⬝ᵥ (⇑v : Fin d → ℂ))).re = hH.eigenvalues i := by
    rw [Complex.real_smul, Complex.re_ofReal_mul, hn, mul_one]
  rw [this] at h1
  exact le_trans (le_abs_self _) h1

lemma pow_facts {d : ℕ} {R : Mat d} (hR : R.PosSemidef) (htr : tr R ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hnorm : opNorm R ≤ β) (m : ℕ) (hm : 1 ≤ m) :
    (R^m).trace.im = 0 ∧ 0 ≤ (R^m).trace.re ∧ (R^m).trace.re ≤ 1 ∧ (R^m).trace.re ≤ β^(m-1) := by
  have hH := hR.1
  have hpow : R^m = cfc (fun x : ℝ => x^m) R := (cfc_pow_id R m hH.isSelfAdjoint).symm
  have htrm : (R^m).trace = ∑ i, (((hH.eigenvalues i)^m : ℝ) : ℂ) := by
    rw [hpow, trace_cfc hH]
  have htr1 : (R.trace).re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  have hl0 : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hR.eigenvalues_nonneg i
  have hsum : ∑ i, hH.eigenvalues i ≤ 1 := by rw [← htr1]; exact htr
  have hl1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ i)) hsum
  have hlb : ∀ i, hH.eigenvalues i ≤ β := fun i => le_trans (eig_le_opNorm hH i) hnorm
  rw [htrm]
  simp only [Complex.im_sum, Complex.ofReal_im, Finset.sum_const_zero, Complex.re_sum,
    Complex.ofReal_re, true_and]
  refine ⟨Finset.sum_nonneg (fun i _ => pow_nonneg (hl0 i) _), ?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hsum
    calc (hH.eigenvalues i)^m ≤ (hH.eigenvalues i)^1 := pow_le_pow_of_le_one (hl0 i) (hl1 i) hm
      _ = _ := pow_one _
  · have : ∀ i, (hH.eigenvalues i)^m ≤ hH.eigenvalues i * β^(m-1) := by
      intro i
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m-1, by omega⟩
      rw [pow_succ, mul_comm, Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hl0 i) (hlb i) k) (hl0 i)
    refine le_trans (Finset.sum_le_sum (fun i _ => this i)) ?_
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (pow_nonneg hβ _) hsum


/-- `n - (number of cycles)`, defined by splicing out `0` recursively. -/
def dcyc : (n : ℕ) → Perm (Fin n) → ℕ
  | 0, _ => 0
  | n+1, σ => dcyc n (Perm.decomposeFin σ).2 + if (Perm.decomposeFin σ).1 = 0 then 0 else 1

lemma dcyc_symm {n : ℕ} (p : Fin (n+1)) (e : Perm (Fin n)) :
    dcyc (n+1) (Perm.decomposeFin.symm (p, e)) = dcyc n e + if p = 0 then 0 else 1 := by
  simp [dcyc]

lemma sum_dcyc (β : ℝ) : ∀ n : ℕ, ∑ σ : Perm (Fin n), β^(dcyc n σ) =
    ∏ l ∈ Finset.range n, (1 + (l:ℝ)*β)
  | 0 => by simp [dcyc]
  | n+1 => by
    rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
    simp only [dcyc_symm, pow_add]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_dcyc β n, Finset.prod_range_succ]
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [if_true, pow_zero, Fin.succ_ne_zero, if_false, pow_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma T_nil {ι : Type*} [Fintype ι] (M : Fin 0 → Matrix ι ι ℂ) (σ : Perm (Fin 0)) : T 0 M σ = 1 := by
  simp [T]

lemma T_bound {d : ℕ} {R : Mat d} {β : ℝ} (hβ : 0 < β)
    (hp : ∀ m, 1 ≤ m → (R^m).trace.im = 0 ∧ 0 ≤ (R^m).trace.re ∧ (R^m).trace.re ≤ 1 ∧
      (R^m).trace.re ≤ β^(m-1)) :
    ∀ (n : ℕ) (e : Fin n → ℕ), (∀ i, 1 ≤ e i) → ∀ σ : Perm (Fin n),
      (T n (fun i => R^(e i)) σ).im = 0 ∧ 0 ≤ (T n (fun i => R^(e i)) σ).re ∧
      (T n (fun i => R^(e i)) σ).re ≤ 1 ∧
      (T n (fun i => R^(e i)) σ).re ≤ β^((∑ i, (e i - 1)) + dcyc n σ)
  | 0, e, he, σ => by simp [T_nil, dcyc]
  | n+1, e, he, σ => by
    obtain ⟨⟨p, e'⟩, rfl⟩ : ∃ pe, Perm.decomposeFin.symm pe = σ := ⟨Perm.decomposeFin σ, by simp⟩
    rw [dcyc_symm]
    refine Fin.cases ?_ (fun q => ?_) p
    · rw [T_zero]
      obtain ⟨a1, a2, a3, a4⟩ := hp (e 0) (he 0)
      obtain ⟨b1, b2, b3, b4⟩ := T_bound hβ hp n (fun i => e i.succ) (fun i => he _) e'
      set a := (R^(e 0)).trace
      set b := T n (fun i => R^(e i.succ)) e'
      have hre : (a * b).re = a.re * b.re := by rw [Complex.mul_re, a1, zero_mul, sub_zero]
      refine ⟨by rw [Complex.mul_im, a1, b1]; ring, by rw [hre]; positivity, ?_, ?_⟩
      · rw [hre]; nlinarith
      · rw [hre, Fin.sum_univ_succ, if_pos rfl, add_zero]
        calc a.re * b.re ≤ β^(e 0 - 1) * β^((∑ i : Fin n, (e i.succ - 1)) + dcyc n e') :=
              mul_le_mul a4 b4 b2 (pow_nonneg hβ.le _)
          _ = _ := by rw [← pow_add]; ring_nf
    · rw [T_succ]
      set e'' : Fin n → ℕ := fun i => if i = q then e i.succ + e 0 else e i.succ with he''
      have hM : (fun i : Fin n => if i = q then R^(e i.succ) * R^(e 0) else R^(e i.succ)) =
          fun i => R^(e'' i) := by
        funext i; by_cases h : i = q <;> simp [he'', h, pow_add]
      rw [hM]
      obtain ⟨b1, b2, b3, b4⟩ := T_bound hβ hp n e'' (fun i => by
        simp only [he'']; split_ifs <;> have := he i.succ <;> omega) e'
      refine ⟨b1, b2, b3, le_trans b4 (le_of_eq ?_)⟩
      congr 1
      have hsum : ∑ i, (e'' i - 1) = ∑ i : Fin n, (e i.succ - 1) + e 0 := by
        have : ∀ i, e'' i - 1 = (e i.succ - 1) + (if i = q then e 0 else 0) := by
          intro i; simp only [he'']; split_ifs <;> have := he i.succ <;> omega
        simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hsum, Fin.sum_univ_succ, if_neg (Fin.succ_ne_zero q)]
      have := he 0
      omega


lemma trace_perm {d j : ℕ} (R : Mat d) (σ : Perm (Fin j)) :
    (powerState R j * permutationOp (ι := Fin d) σ).trace = T j (fun _ => R) σ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, powerState, tensor,
    OptimalSpectrum.Entangled.kronFamily, permutationOp, OptimalSpectrum.Entangled.permOp,
    Matrix.of_apply, mul_ite, mul_one, mul_zero]
  unfold T
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (x ∘ ⇑σ.symm)]
  · rw [if_pos rfl]
    exact (Equiv.prod_comp σ (fun i => R (x i) (x (σ.symm i)))).symm.trans (by simp)
  · intro y _ hy; rw [if_neg]; intro h; exact hy (by rw [h])
  · simp

lemma permOp_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (π π' : Perm (Fin k)) :
    permutationOp (ι := ι) π * permutationOp π' = permutationOp (π * π') := by
  ext x y
  simp only [Matrix.mul_apply, permutationOp, OptimalSpectrum.Entangled.permOp, Matrix.of_apply,
    mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (y ∘ ⇑π'.symm)]
  · simp only [if_true]
    have : y ∘ ⇑(π * π').symm = (y ∘ ⇑π'.symm) ∘ ⇑π.symm := by
      funext a; simp [Perm.mul_def]
    rw [this]
  · intro u _ hu; rw [if_neg hu]
  · simp

def FC (j : ℕ) (π : Perm (Fin j)) : Prop := (j = 1 ∧ π = 1) ∨ (π.IsCycle ∧ π.support = Finset.univ)

lemma card_FC {j : ℕ} (hj : 1 ≤ j) :
    ((Finset.univ.filter (FC j)).card : ℝ) ≤ ((j-1).factorial : ℝ) := by
  rcases Nat.eq_or_lt_of_le hj with h1 | h2
  · subst h1
    have : (Finset.univ.filter (FC 1)).card ≤ 1 := by
      calc _ ≤ (Finset.univ : Finset (Perm (Fin 1))).card := Finset.card_filter_le _ _
        _ = 1 := by simp
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
    exact_mod_cast this
  · have hsub : Finset.univ.filter (FC j) ⊆ Finset.univ.filter (fun g : Perm (Fin j) => g.cycleType = {j}) := by
      intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, FC] at hπ ⊢
      rcases hπ with ⟨h, -⟩ | ⟨hc, hs⟩
      · omega
      · rw [hc.cycleType, hs, Finset.card_univ, Fintype.card_fin]
    have hcard := Perm.card_of_cycleType_singleton (α := Fin j) (n := j) (by omega) (by simp)
    rw [Fintype.card_fin, Nat.choose_self, mul_one] at hcard
    have := Finset.card_le_card hsub
    rw [hcard] at this
    exact_mod_cast this

end OTDLem42

open OptimalTraceDistance.Estimation OTDLem42 Equiv in
theorem solution (d j : ℕ) (hd : 0 < d) (hj : 1 ≤ j)
    (R : Mat d) (hR : R.PosSemidef) (htr : tr R ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hnorm : opNorm R ≤ β) :
  tr (powerState R j * (cycleAverage d j)^2) ≤ min 1 (cycleFactor β j) := by
  set c : ℝ := ((j-1).factorial : ℝ)⁻¹ with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hCA : cycleAverage d j = (c : ℂ) • ∑ π : Perm (Fin j),
      if FC j π then permutationOp (ι := Fin d) π else 0 := by
    unfold cycleAverage; rw [hc]; push_cast
    congr 1
    exact Finset.sum_congr rfl (fun π _ => if_congr Iff.rfl rfl rfl)
  have hsq : (cycleAverage d j)^2 = ((c:ℂ)^2) • ∑ π : Perm (Fin j), ∑ π' : Perm (Fin j),
      if FC j π ∧ FC j π' then permutationOp (ι := Fin d) (π * π') else 0 := by
    rw [hCA, sq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← sq, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π' _ => ?_)
    by_cases h1 : FC j π <;> by_cases h2 : FC j π' <;> simp [h1, h2, permOp_mul]
  have hp := fun m hm => pow_facts hR htr hβ.le hnorm m hm
  have hTb := fun σ => T_bound hβ hp j (fun _ => 1) (fun _ => le_refl 1) σ
  simp only [pow_one, Nat.sub_self, Finset.sum_const_zero, zero_add] at hTb
  set t : Perm (Fin j) → ℝ := fun σ => (T j (fun _ => R) σ).re with ht
  have htr_eq : tr (powerState R j * (cycleAverage d j)^2) =
      c^2 * ∑ π : Perm (Fin j), ∑ π' : Perm (Fin j), if FC j π ∧ FC j π' then t (π * π') else 0 := by
    unfold tr
    rw [hsq, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
    simp only [Matrix.mul_sum, Matrix.trace_sum, mul_ite, Matrix.mul_zero, apply_ite Matrix.trace,
      Matrix.trace_zero, trace_perm]
    rw [smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    congr 1
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun π' _ => ?_))
    split_ifs <;> simp [ht]
  rw [htr_eq]
  have hcard := card_FC hj
  have hcF : c * ((Finset.univ.filter (FC j)).card : ℝ) ≤ 1 := by
    rw [hc, inv_mul_le_iff₀ (by positivity), mul_one]; exact hcard
  refine le_min ?_ ?_
  · -- bound by 1
    have h1 : ∀ π : Perm (Fin j), ∑ π' : Perm (Fin j), (if FC j π ∧ FC j π' then t (π * π') else 0) ≤
        if FC j π then ((Finset.univ.filter (FC j)).card : ℝ) else 0 := by
      intro π
      by_cases hπ : FC j π
      · simp only [hπ, true_and, if_true]
        rw [← Finset.sum_filter]
        calc ∑ π' ∈ Finset.univ.filter (FC j), t (π * π') ≤ ∑ π' ∈ Finset.univ.filter (FC j), (1:ℝ) :=
              Finset.sum_le_sum (fun π' _ => (hTb (π * π')).2.2.1)
          _ = _ := by simp
      · simp [hπ]
    calc c^2 * ∑ π : Perm (Fin j), ∑ π' : Perm (Fin j), (if FC j π ∧ FC j π' then t (π * π') else 0)
        ≤ c^2 * ∑ π : Perm (Fin j), (if FC j π then ((Finset.univ.filter (FC j)).card : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => h1 π)) (by positivity)
      _ = (c * ((Finset.univ.filter (FC j)).card : ℝ))^2 := by
          rw [← Finset.sum_filter]; simp; ring
      _ ≤ 1 := by
          have h0 : 0 ≤ c * ((Finset.univ.filter (FC j)).card : ℝ) := by positivity
          nlinarith
  · -- bound by the cycle factor
    have hall : ∑ σ : Perm (Fin j), t σ ≤ ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) := by
      rw [← sum_dcyc β j]
      exact Finset.sum_le_sum (fun σ _ => (hTb σ).2.2.2)
    have h1 : ∀ π : Perm (Fin j), ∑ π' : Perm (Fin j), (if FC j π ∧ FC j π' then t (π * π') else 0) ≤
        if FC j π then ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) else 0 := by
      intro π
      by_cases hπ : FC j π
      · simp only [hπ, true_and, if_true]
        calc ∑ π' : Perm (Fin j), (if FC j π' then t (π * π') else 0) ≤ ∑ π' : Perm (Fin j), t (π * π') :=
              Finset.sum_le_sum (fun π' _ => by
                split_ifs
                · exact le_refl _
                · exact (hTb _).2.1)
          _ = ∑ σ : Perm (Fin j), t σ := Equiv.sum_comp (Equiv.mulLeft π) t
          _ ≤ _ := hall
      · simp [hπ]
    have hP0 : 0 ≤ ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) :=
      Finset.prod_nonneg (fun l _ => by positivity)
    calc c^2 * ∑ π : Perm (Fin j), ∑ π' : Perm (Fin j), (if FC j π ∧ FC j π' then t (π * π') else 0)
        ≤ c^2 * ∑ π : Perm (Fin j), (if FC j π then ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) else 0) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => h1 π)) (by positivity)
      _ = c * (c * ((Finset.univ.filter (FC j)).card : ℝ)) * ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) := by
          rw [← Finset.sum_filter]; simp; ring
      _ ≤ c * 1 * ∏ l ∈ Finset.range j, (1 + (l:ℝ)*β) := by gcongr
      _ = cycleFactor β j := by unfold cycleFactor; rw [hc]; ring
