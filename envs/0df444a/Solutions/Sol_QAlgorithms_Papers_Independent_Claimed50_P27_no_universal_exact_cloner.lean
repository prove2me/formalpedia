-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P27.no_universal_exact_cloner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:44:59.76112+00:00
-- url     : https://prove2.me/submissions/cf17a8d3-c878-4f49-ae98-c7f7f8587f87

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27
noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma g67g_pair (a : PairReg 3 → ℝ) (h0 : ∀ y, 0 ≤ a y) (h1 : ∑ y, a y = 1)
    (y1 y2 : PairReg 3) (hne : y1 ≠ y2) : a y1 + a y2 ≤ 1 := by
  rw [← h1, ← Finset.sum_pair hne]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => h0 y)

def g67g_perm (f g : Fin 3 → Fin 3) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 3) := ⟨f, g, h1, h2⟩

lemma g67g_classical : ¬ ∃ net : ClassicalOneCall, ∀ f : Equiv.Perm (Fin 3), ∀ x : PairReg 3,
      net.probability f x (f x.1,f x.2) = 1 := by
  rintro ⟨net, h⟩
  have e := fun (f g : Fin 3 → Fin 3) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) =>
    h (g67g_perm f g h1 h2) (0, 1)
  have e1 := e ![0,1,2] ![0,1,2] (by decide) (by decide)
  have e2 := e ![1,0,2] ![1,0,2] (by decide) (by decide)
  have e3 := e ![2,1,0] ![2,1,0] (by decide) (by decide)
  have e4 := e ![0,2,1] ![0,2,1] (by decide) (by decide)
  have e5 := e ![1,2,0] ![2,0,1] (by decide) (by decide)
  have e6 := e ![2,0,1] ![1,2,0] (by decide) (by decide)
  simp only [ClassicalOneCall.probability, g67g_perm, Equiv.coe_fn_mk, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e1 e2 e3 e4 e5 e6
  have P := fun q r y1 y2 (hne : y1 ≠ y2) =>
    mul_le_mul_of_nonneg_left (g67g_pair (net.output (0,1) q r) (net.output_nonnegative _ _ _)
      (net.output_total _ _ _) y1 y2 hne) (net.query_nonnegative (0,1) q)
  have a1 := P 0 0 (0,1) (0,2) (by decide)
  have a2 := P 0 1 (1,0) (1,2) (by decide)
  have a3 := P 0 2 (2,1) (2,0) (by decide)
  have b1 := P 1 1 (0,1) (2,1) (by decide)
  have b2 := P 1 0 (1,0) (2,0) (by decide)
  have b3 := P 1 2 (0,2) (1,2) (by decide)
  have c1 := P 2 2 (0,1) (1,0) (by decide)
  have c2 := P 2 0 (2,1) (1,2) (by decide)
  have c3 := P 2 1 (0,2) (2,0) (by decide)
  have hq := net.query_total (0,1)
  simp only [Fin.sum_univ_three] at hq
  nlinarith

lemma g67g_kraus_lin {ι κ : Type*} [Fintype ι] {m : ℕ} (E : Fin m → Matrix κ ι ℂ)
    (A B C D : Matrix ι ι ℂ) :
    krausApply E A - krausApply E B + krausApply E C - krausApply E D =
      krausApply E (A - B + C - D) := by
  simp only [krausApply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul]

def g67g_D {d : ℕ} (i0 : Fin d) (c : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun j => if j = i0 then c else 1)

lemma g67g_D_unit {d : ℕ} (i0 : Fin d) (c : ℂ) (hc : c * conj c = 1) :
    g67g_D i0 c ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [g67g_D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext j
  by_cases h : j = i0 <;> simp [h, hc]

lemma g67g_conjD {d : ℕ} (i0 : Fin d) (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) :
    conjSuperop (g67g_D i0 c) M p q =
      (if p = i0 then c else 1) * M p q * conj (if q = i0 then c else 1) := by
  simp [conjSuperop, g67g_D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal]

lemma g67g_conj_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℂ) (M : Matrix ι ι ℂ) (p q : ι) :
    conjSuperop (Matrix.diagonal a) M p q = a p * M p q * conj (a q) := by
  simp [conjSuperop, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]

lemma g67g_kron_diag {ι : Type*} [DecidableEq ι] (a b : ι → ℂ) :
    Matrix.kronecker (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun x : ι × ι => a x.1 * b x.2) := by
  ext x y
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Prod.ext_iff]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2]

lemma g67g_onFirst_apply {I O M : Type*} (Phi : Superop I O) (Y : Matrix (I × M) (I × M) ℂ)
    (a b : O × M) : onFirst Phi Y a b = Phi (Matrix.of fun i j => Y (i, a.2) (j, b.2)) a.1 b.1 := rfl

lemma g67g_zero {d : ℕ} {M : Type*} (i0 : Fin d) (Y : Matrix (Fin d × M) (Fin d × M) ℂ) :
    onFirst (conjSuperop (g67g_D i0 1)) Y - onFirst (conjSuperop (g67g_D i0 Complex.I)) Y +
      onFirst (conjSuperop (g67g_D i0 (-1))) Y - onFirst (conjSuperop (g67g_D i0 (-Complex.I))) Y
      = 0 := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, g67g_onFirst_apply, Matrix.zero_apply, g67g_D,
    g67g_conj_diag, Matrix.of_apply]
  by_cases ha : a.1 = i0 <;> by_cases hb : b.1 = i0 <;> simp [ha, hb] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

lemma g67g_quantum (d : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ net : OneCall d, ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), OneCall.run net U = targetChannel U := by
  rintro ⟨net, h⟩
  obtain ⟨m, E, -, hE⟩ := net.post_channel
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  have hc1 : (1 : ℂ) * conj 1 = 1 := by simp
  have hc2 : Complex.I * conj Complex.I = 1 := by simp
  have hc3 : (-1 : ℂ) * conj (-1) = 1 := by simp
  have hc4 : (-Complex.I) * conj (-Complex.I) = 1 := by simp
  let W : (c : ℂ) → c * conj c = 1 → Matrix.unitaryGroup (Fin d) ℂ :=
    fun c hc => ⟨g67g_D i0 c, g67g_D_unit i0 c hc⟩
  let ρ0 : Matrix (PairReg d) (PairReg d) ℂ := Matrix.single (i0, i0) (i1, i1) 1
  have htarget : ∀ c hc, targetChannel (W c hc) ρ0 (i0, i0) (i1, i1) = c ^ 2 := by
    intro c hc
    simp only [targetChannel, W, g67g_D, g67g_kron_diag, g67g_conj_diag, ρ0, Matrix.single_apply]
    simp [h01]
    ring
  have hrun : ∀ c hc, targetChannel (W c hc) ρ0 =
      krausApply E (onFirst (conjSuperop (g67g_D i0 c)) (net.pre ρ0)) := by
    intro c hc
    rw [← h (W c hc)]
    simp only [OneCall.run, DeviceCloner.run, Function.comp_apply]
    exact hE _
  have hzero := g67g_zero i0 (net.pre ρ0)
  have key := g67g_kraus_lin E
    (onFirst (conjSuperop (g67g_D i0 1)) (net.pre ρ0))
    (onFirst (conjSuperop (g67g_D i0 Complex.I)) (net.pre ρ0))
    (onFirst (conjSuperop (g67g_D i0 (-1))) (net.pre ρ0))
    (onFirst (conjSuperop (g67g_D i0 (-Complex.I))) (net.pre ρ0))
  rw [hzero, ← hrun 1 hc1, ← hrun _ hc2, ← hrun _ hc3, ← hrun _ hc4] at key
  have := congrFun (congrFun key (i0, i0)) (i1, i1)
  simp only [Matrix.sub_apply, Matrix.add_apply, htarget] at this
  simp only [krausApply, Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero,
    Matrix.zero_apply] at this
  ring_nf at this
  simp [Complex.I_sq] at this

/-- PDF p.1: the two distinct corollaries. The first is ordinary classical access
to all three-letter permutations; the second is a common deterministic quantum
network for all d-dimensional unitary channels, compared modulo global phase. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (¬ ∃ net : ClassicalOneCall, ∀ f : Equiv.Perm (Fin 3), ∀ x : PairReg 3,
      net.probability f x (f x.1,f x.2) = 1) ∧
    (¬ ∃ net : OneCall d, ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), OneCall.run net U = targetChannel U) := ⟨g67g_classical, g67g_quantum d hd⟩


end
