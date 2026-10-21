-- Prove2me | solution 1 for SaddleSplit.Async.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T17:12:15.381299+00:00
-- url     : https://prove2.me/submissions/ce079459-9430-453b-835c-8d25dee69ebd

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting
import Theorems.Thm_SaddleSplit_Async_proposition_2_6
import Theorems.Thm_SaddleSplit_Async_proposition_2_2_iii_iv
import Theorems.Thm_SaddleSplit_Async_lemma_A_1
import Theorems.Thm_SaddleSplit_Async_lemma_A_2
import Theorems.Thm_SaddleSplit_Async_lemma_A_3

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section XS
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem xs_eta (X : XSpace H G) : mkX (pX X) (pY X) (pZ X) (pV X) = X := rfl

theorem xs_ext {X X' : XSpace H G} (h1 : pX X = pX X') (h2 : pY X = pY X')
    (h3 : pZ X = pZ X') (h4 : pV X = pV X') : X = X' := by
  rw [← xs_eta X, ← xs_eta X', h1, h2, h3, h4]

@[simp] theorem pX_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pX (mkX x y z v) = x := rfl
@[simp] theorem pY_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pY (mkX x y z v) = y := rfl
@[simp] theorem pZ_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pZ (mkX x y z v) = z := rfl
@[simp] theorem pV_mkX (x : PiLp 2 H) (y z v : PiLp 2 G) : pV (mkX x y z v) = v := rfl
@[simp] theorem pX_add (X X' : XSpace H G) : pX (X + X') = pX X + pX X' := rfl
@[simp] theorem pY_add (X X' : XSpace H G) : pY (X + X') = pY X + pY X' := rfl
@[simp] theorem pZ_add (X X' : XSpace H G) : pZ (X + X') = pZ X + pZ X' := rfl
@[simp] theorem pV_add (X X' : XSpace H G) : pV (X + X') = pV X + pV X' := rfl
@[simp] theorem pX_sub (X X' : XSpace H G) : pX (X - X') = pX X - pX X' := rfl
@[simp] theorem pY_sub (X X' : XSpace H G) : pY (X - X') = pY X - pY X' := rfl
@[simp] theorem pZ_sub (X X' : XSpace H G) : pZ (X - X') = pZ X - pZ X' := rfl
@[simp] theorem pV_sub (X X' : XSpace H G) : pV (X - X') = pV X - pV X' := rfl
@[simp] theorem pX_smul (c : ℝ) (X : XSpace H G) : pX (c • X) = c • pX X := rfl
@[simp] theorem pY_smul (c : ℝ) (X : XSpace H G) : pY (c • X) = c • pY X := rfl
@[simp] theorem pZ_smul (c : ℝ) (X : XSpace H G) : pZ (c • X) = c • pZ X := rfl
@[simp] theorem pV_smul (c : ℝ) (X : XSpace H G) : pV (c • X) = c • pV X := rfl
@[simp] theorem pX_zero : pX (0 : XSpace H G) = 0 := rfl
@[simp] theorem pY_zero : pY (0 : XSpace H G) = 0 := rfl
@[simp] theorem pZ_zero : pZ (0 : XSpace H G) = 0 := rfl
@[simp] theorem pV_zero : pV (0 : XSpace H G) = 0 := rfl

theorem xs_inner4 (X X' : XSpace H G) : ⟪X, X'⟫_ℝ =
    ⟪pX X, pX X'⟫_ℝ + ⟪pY X, pY X'⟫_ℝ + ⟪pZ X, pZ X'⟫_ℝ + ⟪pV X, pV X'⟫_ℝ := by
  simp only [WithLp.prod_inner_apply, pX, pY, pZ, pV]; ring

theorem xs_inner (X X' : XSpace H G) : ⟪X, X'⟫_ℝ =
    ∑ i, ⟪pX X i, pX X' i⟫_ℝ + ∑ k, ⟪pY X k, pY X' k⟫_ℝ + ∑ k, ⟪pZ X k, pZ X' k⟫_ℝ
      + ∑ k, ⟪pV X k, pV X' k⟫_ℝ := by
  rw [xs_inner4]; simp only [PiLp.inner_apply]

theorem xs_normsq4 (X : XSpace H G) : ‖X‖ ^ 2 =
    ‖pX X‖ ^ 2 + ‖pY X‖ ^ 2 + ‖pZ X‖ ^ 2 + ‖pV X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, xs_inner4]
  simp only [real_inner_self_eq_norm_sq]

theorem xs_normsq (X : XSpace H G) : ‖X‖ ^ 2 =
    ∑ i, ‖pX X i‖ ^ 2 + ∑ k, ‖pY X k‖ ^ 2 + ∑ k, ‖pZ X k‖ ^ 2 + ∑ k, ‖pV X k‖ ^ 2 := by
  rw [xs_normsq4]; simp only [PiLp.norm_sq_eq_of_L2]

theorem norm_pX_le (X : XSpace H G) : ‖pX X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pX X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pY_le (X : XSpace H G) : ‖pY X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pY X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pX X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pZ_le (X : XSpace H G) : ‖pZ X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pZ X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pX X‖, sq_nonneg ‖pV X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pV_le (X : XSpace H G) : ‖pV X‖ ≤ ‖X‖ := by
  have := xs_normsq4 X
  have h : ‖pV X‖ ^ 2 ≤ ‖X‖ ^ 2 := by nlinarith [sq_nonneg ‖pY X‖, sq_nonneg ‖pZ X‖, sq_nonneg ‖pX X‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h
theorem norm_pXi_le (X : XSpace H G) (i : I) : ‖pX X i‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ i).trans (norm_pX_le X)
theorem norm_pYk_le (X : XSpace H G) (k : K) : ‖pY X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pY_le X)
theorem norm_pZk_le (X : XSpace H G) (k : K) : ‖pZ X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pZ_le X)
theorem norm_pVk_le (X : XSpace H G) (k : K) : ‖pV X k‖ ≤ ‖X‖ :=
  (PiLp.norm_apply_le _ k).trans (norm_pV_le X)

/-- if every block coordinate is bounded by `c`, the norm is bounded. -/
theorem xs_norm_le_of_blocks (W : XSpace H G) (c : ℝ) (hc : 0 ≤ c)
    (hx : ∀ i, ‖pX W i‖ ≤ c) (hy : ∀ k, ‖pY W k‖ ≤ c) (hz : ∀ k, ‖pZ W k‖ ≤ c)
    (hv : ∀ k, ‖pV W k‖ ≤ c) :
    ‖W‖ ≤ Real.sqrt (Fintype.card I + 3 * Fintype.card K) * c := by
  have hsq : ‖W‖ ^ 2 ≤ (Fintype.card I + 3 * Fintype.card K) * c ^ 2 := by
    rw [xs_normsq]
    have h1 : ∑ i, ‖pX W i‖ ^ 2 ≤ ∑ _i : I, c ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    have h2 : ∑ k, ‖pY W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hy k) 2
    have h3 : ∑ k, ‖pZ W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
    have h4 : ∑ k, ‖pV W k‖ ^ 2 ≤ ∑ _k : K, c ^ 2 :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hv k) 2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1 h2 h3 h4
    nlinarith
  calc ‖W‖ = Real.sqrt (‖W‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card I + 3 * Fintype.card K) * c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

end XS


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section T1
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

/-- most recent activation of block `i` up to `n`. -/
def tbI (prm : Alg34Params I K) (i : I) (n : ℕ) : ℕ := Nat.findGreatest (fun j => i ∈ prm.In j) n
/-- most recent activation of block `k` up to `n`. -/
def tbK (prm : Alg34Params I K) (k : K) (n : ℕ) : ℕ := Nat.findGreatest (fun j => k ∈ prm.Kn j) n
/-- `ϑ_i(n) = π_i(ϑ̄_i(n))`. -/
def thI (prm : Alg34Params I K) (i : I) (n : ℕ) : ℕ := prm.π i (tbI prm i n)
/-- `ϱ_k(n) = ω_k(ϱ̄_k(n))`. -/
def thK (prm : Alg34Params I K) (k : K) (n : ℕ) : ℕ := prm.ω k (tbK prm k n)

theorem carryI (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G)
    (hrun : IsAlg34Run P α prm JA JB JD st) (h0 : prm.In 0 = Finset.univ) (i : I) (n : ℕ) :
    i ∈ prm.In (tbI prm i n) ∧ st.a n i = st.a (tbI prm i n) i ∧
      st.astar n i = st.astar (tbI prm i n) i ∧ st.ξ n i = st.ξ (tbI prm i n) i := by
  induction n with
  | zero => simp [tbI, h0]
  | succ n ih =>
    by_cases h : i ∈ prm.In (n + 1)
    · have : tbI prm i (n + 1) = n + 1 := Nat.findGreatest_eq h
      rw [this]; exact ⟨h, rfl, rfl, rfl⟩
    · have e : tbI prm i (n + 1) = tbI prm i n := Nat.findGreatest_of_not h
      obtain ⟨c1, c2, c3⟩ := (hrun n).2.1 i h
      rw [e, c1, c2, c3]; exact ih

theorem carryK (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G)
    (hrun : IsAlg34Run P α prm JA JB JD st) (h0 : prm.Kn 0 = Finset.univ) (k : K) (n : ℕ) :
    k ∈ prm.Kn (tbK prm k n) ∧ st.b n k = st.b (tbK prm k n) k ∧
      st.d n k = st.d (tbK prm k n) k ∧ st.estar n k = st.estar (tbK prm k n) k ∧
      st.qstar n k = st.qstar (tbK prm k n) k ∧ st.tstar n k = st.tstar (tbK prm k n) k ∧
      st.η n k = st.η (tbK prm k n) k := by
  induction n with
  | zero => simp [tbK, h0]
  | succ n ih =>
    by_cases h : k ∈ prm.Kn (n + 1)
    · have : tbK prm k (n + 1) = n + 1 := Nat.findGreatest_eq h
      rw [this]; exact ⟨h, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · have e : tbK prm k (n + 1) = tbK prm k n := Nat.findGreatest_of_not h
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := (hrun n).2.2.2.1 k h
      rw [e, c1, c2, c3, c4, c5, c6]; exact ih

/-- the `I`-block assignments, read at the most recent activation. -/
theorem factI (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G)
    (hrun : IsAlg34Run P α prm JA JB JD st) (h0 : prm.In 0 = Finset.univ) (i : I) (n : ℕ) :
    let m := thI prm i n
    let l := P.Q i (st.x m i) + P.R (st.x m) i + P.Ladj (st.v m) i
    st.a n i = JA i (prm.γ i m) (st.x m i + prm.γ i m • (P.s i - l - P.C i (st.x m i))) ∧
    st.astar n i = (prm.γ i m)⁻¹ • (st.x m i - st.a n i) - l + P.Q i (st.a n i) ∧
    st.ξ n i = ‖st.a n i - st.x m i‖ ^ 2 := by
  obtain ⟨hmem, c1, c2, c3⟩ := carryI P α prm JA JB JD st hrun h0 i n
  have h := (hrun (tbI prm i n)).1 i hmem
  simp only at h
  obtain ⟨e1, e2, e3⟩ := h
  simp only [thI]
  rw [c1, c2, c3]
  exact ⟨e1, e2, e3⟩

/-- the `K`-block assignments, read at the most recent activation. -/
theorem factK (P : Problem H G) (α : ℝ) (prm : Alg34Params I K)
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k) (st : Alg34State H G)
    (hrun : IsAlg34Run P α prm JA JB JD st) (h0 : prm.Kn 0 = Finset.univ) (k : K) (n : ℕ) :
    let m := thK prm k n
    let us := st.v m k - P.Bl k (st.y m k)
    let ws := st.v m k - P.Dl k (st.z m k)
    st.b n k = JB k (prm.μ k m) (st.y m k + prm.μ k m • (us - P.Bc k (st.y m k))) ∧
    st.d n k = JD k (prm.ν k m) (st.z m k + prm.ν k m • (ws - P.Dc k (st.z m k))) ∧
    st.estar n k = prm.sig k m • (P.Lx (st.x m) k - st.y m k - st.z m k - P.r k) + st.v m k ∧
    st.qstar n k = (prm.μ k m)⁻¹ • (st.y m k - st.b n k) + us + P.Bl k (st.b n k)
      - st.estar n k ∧
    st.tstar n k = (prm.ν k m)⁻¹ • (st.z m k - st.d n k) + ws + P.Dl k (st.d n k)
      - st.estar n k ∧
    st.η n k = ‖st.b n k - st.y m k‖ ^ 2 + ‖st.d n k - st.z m k‖ ^ 2 := by
  obtain ⟨hmem, c1, c2, c3, c4, c5, c6⟩ := carryK P α prm JA JB JD st hrun h0 k n
  have h := (hrun (tbK prm k n)).2.2.1 k hmem
  simp only at h
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
  simp only [thK]
  rw [c1, c2, c3, c4, c5, c6]
  exact ⟨e1, e2, e3, e4, e5, e6⟩

end T1


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section T2
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

def sX (st : Alg34State H G) (n : ℕ) : XSpace H G := mkX (st.x n) (st.y n) (st.z n) (st.v n)
def sP (st : Alg34State H G) (n : ℕ) : XSpace H G := mkX (st.a n) (st.b n) (st.d n) (st.estar n)
def sPs (P : Problem H G) (prm : Alg34Params I K) (st : Alg34State H G) (n : ℕ) : XSpace H G :=
  mkX (WithLp.toLp 2 fun i => st.pstar n i - P.C i (st.x (thI prm i n) i))
    (WithLp.toLp 2 fun k => st.qstar n k - P.Bc k (st.y (thK prm k n) k))
    (WithLp.toLp 2 fun k => st.tstar n k - P.Dc k (st.z (thK prm k n) k)) (st.e n)
def sQ (prm : Alg34Params I K) (st : Alg34State H G) (n : ℕ) : XSpace H G :=
  mkX (WithLp.toLp 2 fun i => st.x (thI prm i n) i) (WithLp.toLp 2 fun k => st.y (thK prm k n) k)
    (WithLp.toLp 2 fun k => st.z (thK prm k n) k) (st.estar n)
def sT (st : Alg34State H G) (n : ℕ) : XSpace H G :=
  mkX (st.pstar n) (st.qstar n) (st.tstar n) (st.e n)

theorem smul_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : ℝ) (hγ : γ ≠ 0)
    (x w a : E) : γ⁻¹ • (x + γ • w - a) = γ⁻¹ • (x - a) + w := by
  rw [show x + γ • w - a = (x - a) + γ • w by abel, smul_add, smul_smul, inv_mul_cancel₀ hγ,
    one_smul]

theorem isOuterRun (P : Problem H G) (α σ ε : ℝ) (prm : Alg34Params I K)
    (h31 : Assumption31 P α σ ε prm) (hI0 : prm.In 0 = Finset.univ)
    (hK0 : prm.Kn 0 = Finset.univ)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k)
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (P.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (P.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (P.Dm k) (JD k γ))
    (st : Alg34State H G) (hrun : IsAlg34Run P α prm JA JB JD st) :
    IsOuterApproxRun P α ε (sX st) (sP st) (sPs P prm st) (sQ prm st) (sT st) st.Δ prm.lam := by
  obtain ⟨-, -, hε0, -, -, -, -, -, hγ, hμν⟩ := h31
  intro n
  obtain ⟨-, -, -, -, he, hps, hΔ, hpos, hnpos⟩ := hrun n
  refine ⟨⟨fun i => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- x-block of gra 𝐌
    obtain ⟨e1, e2, -⟩ := factI P α prm JA JB JD st hrun hI0 i n
    set m := thI prm i n
    have hg : 0 < prm.γ i m := lt_of_lt_of_le hε0 (hγ i m).1
    set l := P.Q i (st.x m i) + P.R (st.x m) i + P.Ladj (st.v m) i
    set u := st.x m i + prm.γ i m • (P.s i - l - P.C i (st.x m i))
    have hres := hJA i (prm.γ i m) hg u
    rw [← e1] at hres
    refine ⟨_, hres, ?_⟩
    simp only [sPs, sP, pX_mkX, pV_mkX, PiLp.toLp_apply]
    rw [hps i, e2, smul_aux _ hg.ne']
    abel
  · obtain ⟨e1, -, -, e4, -, -⟩ := factK P α prm JA JB JD st hrun hK0 k n
    set m := thK prm k n
    have hg : 0 < prm.μ k m := lt_of_lt_of_le hε0 (hμν k m).1.1
    set u := st.y m k + prm.μ k m • (st.v m k - P.Bl k (st.y m k) - P.Bc k (st.y m k))
    have hres := hJB k (prm.μ k m) hg u
    rw [← e1] at hres
    refine ⟨_, hres, ?_⟩
    simp only [sPs, sP, pY_mkX, pV_mkX, PiLp.toLp_apply]
    rw [e4, smul_aux _ hg.ne']
    abel
  · obtain ⟨-, e2, -, -, e5, -⟩ := factK P α prm JA JB JD st hrun hK0 k n
    set m := thK prm k n
    have hg : 0 < prm.ν k m := lt_of_lt_of_le hε0 (hμν k m).2.1.1
    set u := st.z m k + prm.ν k m • (st.v m k - P.Dl k (st.z m k) - P.Dc k (st.z m k))
    have hres := hJD k (prm.ν k m) hg u
    rw [← e2] at hres
    refine ⟨_, hres, ?_⟩
    simp only [sPs, sP, pZ_mkX, pV_mkX, PiLp.toLp_apply]
    rw [e5, smul_aux _ hg.ne']
    abel
  · simp only [sPs, sP, pV_mkX, pX_mkX, pY_mkX, pZ_mkX]
    exact he k
  · apply xs_ext
    · ext i; simp [sT, sPs, sQ, opC]
    · ext k; simp [sT, sPs, sQ, opC]
    · ext k; simp [sT, sPs, sQ, opC]
    · ext k; simp [sT, sPs, sQ, opC, mkX, pV]
  · -- Δ
    rw [hΔ, xs_inner, xs_normsq]
    have hξ : ∀ i, st.ξ n i = ‖st.a n i - st.x (thI prm i n) i‖ ^ 2 := fun i =>
      (factI P α prm JA JB JD st hrun hI0 i n).2.2
    have hη : ∀ k, st.η n k = ‖st.b n k - st.y (thK prm k n) k‖ ^ 2
        + ‖st.d n k - st.z (thK prm k n) k‖ ^ 2 := fun k =>
      (factK P α prm JA JB JD st hrun hK0 k n).2.2.2.2.2
    simp only [sX, sP, sQ, sT, pX_sub, pY_sub, pZ_sub, pV_sub, pX_mkX, pY_mkX, pZ_mkX, pV_mkX,
      PiLp.sub_apply, PiLp.toLp_apply, sub_self, norm_zero, hξ, hη, Finset.sum_add_distrib]
    have hc : ∑ k, ⟪st.e n k, st.v n k - st.estar n k⟫_ℝ
        = ∑ k, ⟪st.v n k - st.estar n k, st.e n k⟫_ℝ :=
      Finset.sum_congr rfl fun k _ => real_inner_comm _ _
    rw [hc]; simp; ring
  · intro h
    obtain ⟨hθ, hx, hy, hz, hv⟩ := hpos h
    refine ⟨hlam n, ?_⟩
    have hden : ‖sT st n‖ ^ 2 = ∑ i, ‖st.pstar n i‖ ^ 2
        + ∑ k, (‖st.qstar n k‖ ^ 2 + ‖st.tstar n k‖ ^ 2 + ‖st.e n k‖ ^ 2) := by
      rw [xs_normsq]; simp only [sT, pX_mkX, pY_mkX, pZ_mkX, pV_mkX, Finset.sum_add_distrib]
      ring
    rw [hden, ← hθ]
    apply xs_ext
    · simp only [sX, sT, pX_mkX, pX_sub, pX_smul, hx]
    · simp only [sX, sT, pY_mkX, pY_sub, pY_smul, hy]
    · simp only [sX, sT, pZ_mkX, pZ_sub, pZ_smul, hz]
    · simp only [sX, sT, pV_mkX, pV_sub, pV_smul, hv]
  · intro h
    obtain ⟨hx, hy, hz, hv⟩ := hnpos h
    simp only [sX, hx, hy, hz, hv]

end T2


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

/-- uniformly bounded sequence. -/
def Bd {E : Type*} [Norm E] (f : ℕ → E) : Prop := ∃ M, ∀ n, ‖f n‖ ≤ M

/-- sequence tending to zero. -/
def Tz {E : Type*} [NormedAddCommGroup E] (f : ℕ → E) : Prop := Tendsto f atTop (𝓝 0)

section Calc
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Bd.add {f g : ℕ → E} (hf : Bd f) (hg : Bd g) : Bd (fun n => f n + g n) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun n => (norm_add_le _ _).trans (add_le_add (hM n) (hN n))⟩
theorem Bd.sub {f g : ℕ → E} (hf : Bd f) (hg : Bd g) : Bd (fun n => f n - g n) := by
  obtain ⟨M, hM⟩ := hf; obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun n => (norm_sub_le _ _).trans (add_le_add (hM n) (hN n))⟩
theorem Bd.const (c : E) : Bd (fun _ : ℕ => c) := ⟨‖c‖, fun _ => le_rfl⟩
theorem Bd.comp {f : ℕ → E} (hf : Bd f) (φ : ℕ → ℕ) : Bd (fun n => f (φ n)) := by
  obtain ⟨M, hM⟩ := hf; exact ⟨M, fun n => hM _⟩
theorem Bd.mono {f : ℕ → E} {g : ℕ → F} (hf : Bd f) (h : ∀ n, ‖g n‖ ≤ ‖f n‖) : Bd g := by
  obtain ⟨M, hM⟩ := hf; exact ⟨M, fun n => (h n).trans (hM n)⟩
theorem Bd.lip {f : ℕ → E} (hf : Bd f) (T : E → F) (L : ℝ) (hL0 : 0 ≤ L)
    (hT : ∀ u w, ‖T u - T w‖ ≤ L * ‖u - w‖) : Bd (fun n => T (f n)) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨‖T 0‖ + L * M, fun n => ?_⟩
  have h1 := hT (f n) 0
  rw [sub_zero] at h1
  calc ‖T (f n)‖ = ‖(T (f n) - T 0) + T 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖T (f n) - T 0‖ + ‖T 0‖ := norm_add_le _ _
    _ ≤ L * ‖f n‖ + ‖T 0‖ := by linarith
    _ ≤ ‖T 0‖ + L * M := by nlinarith [hM n]
theorem Bd.sum {ι : Type*} [Fintype ι] {f : ι → ℕ → E} (hf : ∀ j, Bd (f j)) :
    Bd (fun n => ∑ j, f j n) := by
  choose M hM using hf
  exact ⟨∑ j, M j, fun n => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hM j n)⟩

theorem Tz.add {f g : ℕ → E} (hf : Tz f) (hg : Tz g) : Tz (fun n => f n + g n) := by
  show Tendsto _ _ _; simpa using Filter.Tendsto.add hf hg
theorem Tz.sub {f g : ℕ → E} (hf : Tz f) (hg : Tz g) : Tz (fun n => f n - g n) := by
  show Tendsto _ _ _; simpa using Filter.Tendsto.sub hf hg
theorem Tz.neg {f : ℕ → E} (hf : Tz f) : Tz (fun n => -f n) := by
  show Tendsto _ _ _; simpa using Filter.Tendsto.neg hf
theorem Tz.zero : Tz (fun _ : ℕ => (0 : E)) := tendsto_const_nhds
theorem Tz.mono {f : ℕ → E} {g : ℕ → F} (hf : Tz f) (L : ℝ) (h : ∀ n, ‖g n‖ ≤ L * ‖f n‖) :
    Tz g := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have := (tendsto_zero_iff_norm_tendsto_zero.1 hf).const_mul L
  rw [mul_zero] at this
  exact squeeze_zero (fun n => norm_nonneg _) h this
theorem Tz.comp {f : ℕ → E} (hf : Tz f) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    Tz (fun n => f (φ n)) := Filter.Tendsto.comp hf hφ
theorem Tz.sum {ι : Type*} [Fintype ι] {f : ι → ℕ → E} (hf : ∀ j, Tz (f j)) :
    Tz (fun n => ∑ j, f j n) := by
  have := tendsto_finsetSum (Finset.univ : Finset ι) (fun j _ => hf j)
  show Tendsto _ _ _
  simpa using this
theorem Tz.smul_bd {c : ℕ → ℝ} {f : ℕ → E} [Module ℝ E] [NormSMulClass ℝ E] (hc : Bd c)
    (hf : Tz f) : Tz (fun n => c n • f n) := by
  obtain ⟨M, hM⟩ := hc
  refine hf.mono M fun n => ?_
  rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)
theorem Tz.iff_norm {f : ℕ → E} : Tz f ↔ Tendsto (fun n => ‖f n‖) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero
end Calc

section CalcIP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Tz.inner_bd {f g : ℕ → E} (hf : Bd f) (hg : Tz g) :
    Tendsto (fun n => ⟪f n, g n⟫_ℝ) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hf
  have h1 : Tz (fun n => ⟪f n, g n⟫_ℝ) := by
    refine hg.mono M fun n => ?_
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))
  exact h1
end CalcIP

section Blocks
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ j, NormedAddCommGroup (β j)]

theorem Bd.piLp {f : ℕ → PiLp 2 β} (hf : ∀ j, Bd (fun n => f n j)) : Bd f := by
  choose M hM using hf
  refine ⟨Real.sqrt (∑ j, M j ^ 2), fun n => ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg (f n)), PiLp.norm_sq_eq_of_L2]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (hM j n) 2

theorem Bd.apply {f : ℕ → PiLp 2 β} (hf : Bd f) (j : ι) : Bd (fun n => f n j) :=
  hf.mono fun n => PiLp.norm_apply_le _ j

theorem Tz.piLp {f : ℕ → PiLp 2 β} (hf : ∀ j, Tz (fun n => f n j)) : Tz f := by
  rw [Tz.iff_norm]
  have h : Tendsto (fun n => ∑ j, ‖f n j‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun j _ => ((Tz.iff_norm.1 (hf j)).pow 2))
    simpa using this
  have h2 := h.sqrt
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun n => ?_
  rw [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]

theorem Tz.apply {f : ℕ → PiLp 2 β} (hf : Tz f) (j : ι) : Tz (fun n => f n j) :=
  hf.mono 1 fun n => by rw [one_mul]; exact PiLp.norm_apply_le _ j
end Blocks

section XBlocks
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem Bd.xs {f : ℕ → XSpace H G} (h1 : Bd (fun n => pX (f n))) (h2 : Bd (fun n => pY (f n)))
    (h3 : Bd (fun n => pZ (f n))) (h4 : Bd (fun n => pV (f n))) : Bd f := by
  obtain ⟨M1, hM1⟩ := h1; obtain ⟨M2, hM2⟩ := h2; obtain ⟨M3, hM3⟩ := h3; obtain ⟨M4, hM4⟩ := h4
  refine ⟨M1 + M2 + M3 + M4, fun n => ?_⟩
  have hn := xs_normsq4 (f n)
  have a1 := hM1 n; have a2 := hM2 n; have a3 := hM3 n; have a4 := hM4 n
  have b1 := norm_nonneg (pX (f n)); have b2 := norm_nonneg (pY (f n))
  have b3 := norm_nonneg (pZ (f n)); have b4 := norm_nonneg (pV (f n))
  have hsq : ‖f n‖ ^ 2 ≤ (M1 + M2 + M3 + M4) ^ 2 := by nlinarith
  have h0 : 0 ≤ M1 + M2 + M3 + M4 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 (by norm_num)).1 hsq

theorem Tz.xs {f : ℕ → XSpace H G} (h1 : Tz (fun n => pX (f n))) (h2 : Tz (fun n => pY (f n)))
    (h3 : Tz (fun n => pZ (f n))) (h4 : Tz (fun n => pV (f n))) : Tz f := by
  rw [Tz.iff_norm]
  have h : Tendsto (fun n => ‖pX (f n)‖ ^ 2 + ‖pY (f n)‖ ^ 2 + ‖pZ (f n)‖ ^ 2 + ‖pV (f n)‖ ^ 2)
      atTop (𝓝 0) := by
    have := (((Tz.iff_norm.1 h1).pow 2).add ((Tz.iff_norm.1 h2).pow 2)).add
      ((Tz.iff_norm.1 h3).pow 2) |>.add ((Tz.iff_norm.1 h4).pow 2)
    simpa using this
  have h2' := h.sqrt
  rw [Real.sqrt_zero] at h2'
  refine h2'.congr fun n => ?_
  rw [← xs_normsq4, Real.sqrt_sq (norm_nonneg _)]

theorem Bd.pX {f : ℕ → XSpace H G} (hf : Bd f) : Bd (fun n => pX (f n)) :=
  hf.mono fun n => norm_pX_le _
theorem Bd.pY {f : ℕ → XSpace H G} (hf : Bd f) : Bd (fun n => pY (f n)) :=
  hf.mono fun n => norm_pY_le _
theorem Bd.pZ {f : ℕ → XSpace H G} (hf : Bd f) : Bd (fun n => pZ (f n)) :=
  hf.mono fun n => norm_pZ_le _
theorem Bd.pV {f : ℕ → XSpace H G} (hf : Bd f) : Bd (fun n => pV (f n)) :=
  hf.mono fun n => norm_pV_le _
theorem Tz.pX {f : ℕ → XSpace H G} (hf : Tz f) : Tz (fun n => pX (f n)) :=
  hf.mono 1 fun n => by rw [one_mul]; exact norm_pX_le _
theorem Tz.pY {f : ℕ → XSpace H G} (hf : Tz f) : Tz (fun n => pY (f n)) :=
  hf.mono 1 fun n => by rw [one_mul]; exact norm_pY_le _
theorem Tz.pZ {f : ℕ → XSpace H G} (hf : Tz f) : Tz (fun n => pZ (f n)) :=
  hf.mono 1 fun n => by rw [one_mul]; exact norm_pZ_le _
theorem Tz.pV {f : ℕ → XSpace H G} (hf : Tz f) : Tz (fun n => pV (f n)) :=
  hf.mono 1 fun n => by rw [one_mul]; exact norm_pV_le _
end XBlocks


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Helpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coco_lip (β : ℝ) (hβ : 0 < β) (C : E → E) (hC : IsCocoercive β C) (u w : E) :
    ‖C u - C w‖ ≤ β⁻¹ * ‖u - w‖ := by
  have hc := hC u w
  have hcs := real_inner_le_norm (C u - C w) (u - w)
  by_cases h0 : ‖C u - C w‖ = 0
  · rw [h0]; positivity
  · have hp : 0 < ‖C u - C w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [le_inv_mul_iff₀ hβ]
    nlinarith

theorem Bd.smul {c : ℕ → ℝ} {f : ℕ → E} (hc : Bd c) (hf : Bd f) : Bd (fun n => c n • f n) := by
  obtain ⟨M, hM⟩ := hc; obtain ⟨N, hN⟩ := hf
  refine ⟨M * N, fun n => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (hM n) (hN n) (norm_nonneg _) ((norm_nonneg _).trans (hM n))

theorem Bd.of_isBounded {f : ℕ → E} (h : Bornology.IsBounded (Set.range f)) : Bd f := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 h
  exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩

theorem Bd.isBounded {f : ℕ → E} (h : Bd f) : Bornology.IsBounded (Set.range f) := by
  obtain ⟨M, hM⟩ := h
  exact isBounded_iff_forall_norm_le.2 ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩

theorem Bd.real_of_Icc {c : ℕ → ℝ} {lo hi : ℝ} (hlo : 0 ≤ lo) (h : ∀ n, c n ∈ Set.Icc lo hi) :
    Bd c := ⟨hi, fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hlo.trans (h n).1)]; exact (h n).2⟩

theorem Bd.inv_of_Icc {c : ℕ → ℝ} {ε hi : ℝ} (hε : 0 < ε) (h : ∀ n, c n ∈ Set.Icc ε hi) :
    Bd (fun n => (c n)⁻¹) := ⟨ε⁻¹, fun n => by
      have h1 : 0 < c n := lt_of_lt_of_le hε (h n).1
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 h1)]
      exact inv_anti₀ hε (h n).1⟩
end Helpers

section PB
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem Ladj_sub' (P : Problem H G) (v v' : PiLp 2 G) (i : I) :
    P.Ladj v i - P.Ladj v' i = P.Ladj (v - v') i := by
  simp only [Problem.Ladj, ← Finset.sum_sub_distrib, PiLp.sub_apply, map_sub]

theorem Lx_sub' (P : Problem H G) (x x' : PiLp 2 H) (k : K) :
    P.Lx x k - P.Lx x' k = P.Lx (x - x') k := by
  simp only [Problem.Lx, ← Finset.sum_sub_distrib, PiLp.sub_apply, map_sub]

theorem Ladj_skew' (P : Problem H G) (x : PiLp 2 H) (v : PiLp 2 G) :
    ∑ i, ⟪x i, P.Ladj v i⟫_ℝ = ∑ k, ⟪v k, P.Lx x k⟫_ℝ := by
  simp only [Problem.Ladj, Problem.Lx, inner_sum, sum_inner,
    ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem Ladj_bound (P : Problem H G) (v : PiLp 2 G) (i : I) :
    ‖P.Ladj v i‖ ≤ (∑ k, ‖ContinuousLinearMap.adjoint (P.L k i)‖) * ‖v‖ := by
  simp only [Problem.Ladj]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ k) (norm_nonneg _))

theorem Lx_bound (P : Problem H G) (x : PiLp 2 H) (k : K) :
    ‖P.Lx x k‖ ≤ (∑ j, ‖P.L k j‖) * ‖x‖ := by
  simp only [Problem.Lx]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ j) (norm_nonneg _))

theorem Bd.Ladj (P : Problem H G) {v : ℕ → PiLp 2 G} (hv : Bd v) (i : I) :
    Bd (fun n => P.Ladj (v n) i) := by
  obtain ⟨M, hM⟩ := hv
  refine ⟨(∑ k, ‖ContinuousLinearMap.adjoint (P.L k i)‖) * M, fun n => ?_⟩
  exact (Ladj_bound P _ i).trans (mul_le_mul_of_nonneg_left (hM n)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _))

theorem Bd.Lx (P : Problem H G) {x : ℕ → PiLp 2 H} (hx : Bd x) (k : K) :
    Bd (fun n => P.Lx (x n) k) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨(∑ j, ‖P.L k j‖) * M, fun n => ?_⟩
  exact (Lx_bound P _ k).trans (mul_le_mul_of_nonneg_left (hM n)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _))

theorem Tz.Ladj (P : Problem H G) {v : ℕ → PiLp 2 G} (hv : Tz v) (i : I) :
    Tz (fun n => P.Ladj (v n) i) := hv.mono _ fun n => Ladj_bound P _ i

theorem Tz.Lx (P : Problem H G) {x : ℕ → PiLp 2 H} (hx : Tz x) (k : K) :
    Tz (fun n => P.Lx (x n) k) := hx.mono _ fun n => Lx_bound P _ k
end PB


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Main
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

include hprob hD in
theorem m_zer : (zer (saddleOp prob)).Nonempty :=
  ((proposition_2_2_iii_iv prob hprob).2.2.1).1 hD

include hprob h31 in
theorem m_alpha : 0 < α := by
  rcases h31.1.1 with (⟨i, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
  · exact (hprob.1 i).2.1
  · exact (hprob.2.1 k).2.1
  · exact (hprob.2.2.1 k).2.1

include h31 in
theorem m_eps : 0 < ε := h31.2.2.1

include h31 h32 hlam hJA hJB hJD hrun in
theorem m_run : IsOuterApproxRun prob α ε (sX st) (sP st) (sPs prob prm st) (sQ prm st) (sT st)
    st.Δ prm.lam :=
  isOuterRun prob α σ ε prm h31 h32.2.2.1 h32.2.2.2.1 hlam JA JB JD hJA hJB hJD st hrun

include hprob h31 h32 hlam hJA hJB hJD hrun hD in
theorem m_p26 :
    (∀ z ∈ zer (saddleOp prob), ∀ n, ‖sX st (n + 1) - z‖ ≤ ‖sX st n - z‖) ∧
    Summable (fun n => ‖sX st (n + 1) - sX st n‖ ^ 2) ∧
    (Bornology.IsBounded (Set.range (sT st)) → ∀ δ > 0, ∀ᶠ n in atTop, st.Δ n ≤ δ) ∧
    (WeakTendsto (fun n => sX st n - sP st n) 0 →
      Tendsto (fun n => sP st n - sQ prm st n) atTop (𝓝 0) →
      Tendsto (sT st) atTop (𝓝 0) → ∃ z ∈ zer (saddleOp prob), WeakTendsto (sX st) z) :=
  proposition_2_6 prob hprob (m_zer hprob hD) α h31.1 ε ⟨h31.2.2.1, h31.2.2.2.1⟩
  _ _ _ _ _ _ _ (m_run h31 h32 hlam hJA hJB hJD hrun)

include hprob h31 h32 hlam hJA hJB hJD hrun hD in
theorem m_bdX : Bd (sX st) := by
  obtain ⟨z0, hz0⟩ := m_zer hprob hD
  have hF := (m_p26 hprob h31 h32 hlam hJA hJB hJD hrun hD).1
  have hmono : ∀ n, ‖sX st n - z0‖ ≤ ‖sX st 0 - z0‖ := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hF z0 hz0 n).trans ih
  refine ⟨‖sX st 0 - z0‖ + ‖z0‖, fun n => ?_⟩
  calc ‖sX st n‖ = ‖(sX st n - z0) + z0‖ := by rw [sub_add_cancel]
    _ ≤ ‖sX st n - z0‖ + ‖z0‖ := norm_add_le _ _
    _ ≤ _ := by linarith [hmono n]

include hprob h31 h32 hlam hJA hJB hJD hrun hD in
theorem m_summ : Summable (fun n => ‖sX st (n + 1) - sX st n‖ ^ 2) :=
  (m_p26 hprob h31 h32 hlam hJA hJB hJD hrun hD).2.1

-- lag lemma (Lemma A.3) for `I`.
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem m_lagI (i : I) : Tz (fun n => sX st (thI prm i n) - sX st n) := by
  haveI : Nonempty I := ⟨i⟩
  exact lemma_A_3 prm.In h32.1 Pw (sX st) (m_summ hprob h31 h32 hlam hJA hJB hJD hrun hD)
    h32.2.2.1 h32.2.2.2.2.1 T i (prm.π i) (fun n => h33.1 i n)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem m_lagK (k : K) : Tz (fun n => sX st (thK prm k n) - sX st n) := by
  haveI : Nonempty K := ⟨k⟩
  exact lemma_A_3 prm.Kn h32.2.1 Pw (sX st) (m_summ hprob h31 h32 hlam hJA hJB hJD hrun hD)
    h32.2.2.2.1 h32.2.2.2.2.2 T k (prm.ω k) (fun n => h33.2 k n)

end Main


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Bds
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_x : Bd st.x := (m_bdX hprob h31 h32 hlam hJA hJB hJD hrun hD).pX
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_y : Bd st.y := (m_bdX hprob h31 h32 hlam hJA hJB hJD hrun hD).pY
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_z : Bd st.z := (m_bdX hprob h31 h32 hlam hJA hJB hJD hrun hD).pZ
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_v : Bd st.v := (m_bdX hprob h31 h32 hlam hJA hJB hJD hrun hD).pV

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_estar (k : K) : Bd (fun n => st.estar n k) := by
  have e : (fun n => st.estar n k) = fun n =>
      prm.sig k (thK prm k n) • (prob.Lx (st.x (thK prm k n)) k - st.y (thK prm k n) k
        - st.z (thK prm k n) k - prob.r k) + st.v (thK prm k n) k :=
    funext fun n => (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.1
  rw [e]
  have hs : Bd (fun n => prm.sig k (thK prm k n)) :=
    Bd.real_of_Icc (m_eps h31).le (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.2)
  have hx := (b_x hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).comp (thK prm k)
  have hy := ((b_y hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hz := ((b_z hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hv := ((b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  exact (hs.smul ((((hx.Lx prob k).sub hy).sub hz).sub (Bd.const _))).add hv

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_estarL : Bd st.estar := Bd.piLp fun k => b_estar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k

-- the input of the resolvent of 
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_lI (i : I) : Bd (fun n => prob.Q i (st.x (thI prm i n) i) + prob.R (st.x (thI prm i n)) i
    + prob.Ladj (st.v (thI prm i n)) i) := by
  have hx := (b_x hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).comp (thI prm i)
  have hv := (b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).comp (thI prm i)
  have hQ := (hx.apply i).lip (prob.Q i) (prob.αl i) (hprob.1 i).2.2.2.2.1 (hprob.1 i).2.2.2.2.2
  have hR := (hx.lip prob.R prob.χ hprob.2.2.2.2.1 hprob.2.2.2.2.2).apply i
  exact (hQ.add hR).add (hv.Ladj prob i)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_a (i : I) : Bd (fun n => st.a n i) := by
  have e : (fun n => st.a n i) = fun n =>
      JA i (prm.γ i (thI prm i n)) (st.x (thI prm i n) i + prm.γ i (thI prm i n) •
        (prob.s i - (prob.Q i (st.x (thI prm i n) i) + prob.R (st.x (thI prm i n)) i
          + prob.Ladj (st.v (thI prm i n)) i) - prob.C i (st.x (thI prm i n) i))) :=
    funext fun n => (factI prob α prm JA JB JD st hrun h32.2.2.1 i n).1
  rw [e]
  have hε := m_eps h31
  have hγ : ∀ n, prm.γ i (thI prm i n) ∈ Set.Icc ε _ := fun n => h31.2.2.2.2.2.2.2.2.1 i _
  have hgb : Bd (fun n => prm.γ i (thI prm i n)) := Bd.real_of_Icc hε.le hγ
  have hxi := ((b_x hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply i).comp (thI prm i)
  have hC := hxi.lip (prob.C i) (prob.αc i)⁻¹ (inv_nonneg.2 (hprob.1 i).2.1.le)
    (coco_lip _ (hprob.1 i).2.1 _ (hprob.1 i).2.2.1)
  have hu := hxi.add (hgb.smul (((Bd.const (prob.s i)).sub (b_lI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i)).sub hC))
  refine Bd.of_isBounded (lemma_A_1 (prob.A i) (hprob.1 i).1 (JA i) (hJA i) _ hu.isBounded _
    (fun n => lt_of_lt_of_le hε (hγ n).1) hgb.isBounded)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_aL : Bd st.a := Bd.piLp fun i => b_a hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_astar (i : I) : Bd (fun n => st.astar n i) := by
  have e : (fun n => st.astar n i) = fun n =>
      (prm.γ i (thI prm i n))⁻¹ • (st.x (thI prm i n) i - st.a n i)
        - (prob.Q i (st.x (thI prm i n) i) + prob.R (st.x (thI prm i n)) i
          + prob.Ladj (st.v (thI prm i n)) i) + prob.Q i (st.a n i) :=
    funext fun n => (factI prob α prm JA JB JD st hrun h32.2.2.1 i n).2.1
  rw [e]
  have hgi : Bd (fun n => (prm.γ i (thI prm i n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => h31.2.2.2.2.2.2.2.2.1 i _)
  have hxi := ((b_x hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply i).comp (thI prm i)
  have hQa := (b_a hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).lip (prob.Q i) (prob.αl i) (hprob.1 i).2.2.2.2.1 (hprob.1 i).2.2.2.2.2
  exact ((hgi.smul (hxi.sub (b_a hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i))).sub (b_lI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i)).add hQa

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_pstar (i : I) : Bd (fun n => st.pstar n i) := by
  have e : (fun n => st.pstar n i) = fun n =>
      st.astar n i + prob.R (st.a n) i + prob.Ladj (st.estar n) i :=
    funext fun n => (hrun n).2.2.2.2.2.1 i
  rw [e]
  have hR := ((b_aL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).lip prob.R prob.χ hprob.2.2.2.2.1 hprob.2.2.2.2.2).apply i
  exact ((b_astar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).add hR).add ((b_estarL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).Ladj prob i)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_b (k : K) : Bd (fun n => st.b n k) := by
  have e : (fun n => st.b n k) = fun n =>
      JB k (prm.μ k (thK prm k n)) (st.y (thK prm k n) k + prm.μ k (thK prm k n) •
        ((st.v (thK prm k n) k - prob.Bl k (st.y (thK prm k n) k))
          - prob.Bc k (st.y (thK prm k n) k))) :=
    funext fun n => (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).1
  rw [e]
  have hε := m_eps h31
  have hγ : ∀ n, prm.μ k (thK prm k n) ∈ Set.Icc ε _ := fun n => (h31.2.2.2.2.2.2.2.2.2 k _).1
  have hgb : Bd (fun n => prm.μ k (thK prm k n)) := Bd.real_of_Icc hε.le hγ
  have hyk := ((b_y hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hvk := ((b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hBl := hyk.lip (prob.Bl k) (prob.βl k) (hprob.2.1 k).2.2.2.2.1 (hprob.2.1 k).2.2.2.2.2
  have hBc := hyk.lip (prob.Bc k) (prob.βc k)⁻¹ (inv_nonneg.2 (hprob.2.1 k).2.1.le)
    (coco_lip _ (hprob.2.1 k).2.1 _ (hprob.2.1 k).2.2.1)
  have hu := hyk.add (hgb.smul ((hvk.sub hBl).sub hBc))
  exact Bd.of_isBounded (lemma_A_1 (prob.Bm k) (hprob.2.1 k).1 (JB k) (hJB k) _ hu.isBounded _
    (fun n => lt_of_lt_of_le hε (hγ n).1) hgb.isBounded)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_d (k : K) : Bd (fun n => st.d n k) := by
  have e : (fun n => st.d n k) = fun n =>
      JD k (prm.ν k (thK prm k n)) (st.z (thK prm k n) k + prm.ν k (thK prm k n) •
        ((st.v (thK prm k n) k - prob.Dl k (st.z (thK prm k n) k))
          - prob.Dc k (st.z (thK prm k n) k))) :=
    funext fun n => (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.1
  rw [e]
  have hε := m_eps h31
  have hγ : ∀ n, prm.ν k (thK prm k n) ∈ Set.Icc ε _ := fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.1
  have hgb : Bd (fun n => prm.ν k (thK prm k n)) := Bd.real_of_Icc hε.le hγ
  have hzk := ((b_z hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hvk := ((b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hDl := hzk.lip (prob.Dl k) (prob.δl k) (hprob.2.2.1 k).2.2.2.2.1 (hprob.2.2.1 k).2.2.2.2.2
  have hDc := hzk.lip (prob.Dc k) (prob.δc k)⁻¹ (inv_nonneg.2 (hprob.2.2.1 k).2.1.le)
    (coco_lip _ (hprob.2.2.1 k).2.1 _ (hprob.2.2.1 k).2.2.1)
  have hu := hzk.add (hgb.smul ((hvk.sub hDl).sub hDc))
  exact Bd.of_isBounded (lemma_A_1 (prob.Dm k) (hprob.2.2.1 k).1 (JD k) (hJD k) _ hu.isBounded _
    (fun n => lt_of_lt_of_le hε (hγ n).1) hgb.isBounded)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_qstar (k : K) : Bd (fun n => st.qstar n k) := by
  have e : (fun n => st.qstar n k) = fun n =>
      (prm.μ k (thK prm k n))⁻¹ • (st.y (thK prm k n) k - st.b n k)
        + (st.v (thK prm k n) k - prob.Bl k (st.y (thK prm k n) k)) + prob.Bl k (st.b n k)
        - st.estar n k :=
    funext fun n => (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.2.1
  rw [e]
  have hgi : Bd (fun n => (prm.μ k (thK prm k n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).1)
  have hyk := ((b_y hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hvk := ((b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hBl := hyk.lip (prob.Bl k) (prob.βl k) (hprob.2.1 k).2.2.2.2.1 (hprob.2.1 k).2.2.2.2.2
  have hBlb := (b_b hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).lip (prob.Bl k) (prob.βl k) (hprob.2.1 k).2.2.2.2.1
    (hprob.2.1 k).2.2.2.2.2
  exact (((hgi.smul (hyk.sub (b_b hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k))).add (hvk.sub hBl)).add hBlb).sub (b_estar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_tstar (k : K) : Bd (fun n => st.tstar n k) := by
  have e : (fun n => st.tstar n k) = fun n =>
      (prm.ν k (thK prm k n))⁻¹ • (st.z (thK prm k n) k - st.d n k)
        + (st.v (thK prm k n) k - prob.Dl k (st.z (thK prm k n) k)) + prob.Dl k (st.d n k)
        - st.estar n k :=
    funext fun n => (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.2.2.1
  rw [e]
  have hgi : Bd (fun n => (prm.ν k (thK prm k n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.1)
  have hzk := ((b_z hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hvk := ((b_v hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).apply k).comp (thK prm k)
  have hDl := hzk.lip (prob.Dl k) (prob.δl k) (hprob.2.2.1 k).2.2.2.2.1 (hprob.2.2.1 k).2.2.2.2.2
  have hDld := (b_d hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).lip (prob.Dl k) (prob.δl k) (hprob.2.2.1 k).2.2.2.2.1
    (hprob.2.2.1 k).2.2.2.2.2
  exact (((hgi.smul (hzk.sub (b_d hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k))).add (hvk.sub hDl)).add hDld).sub (b_estar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_e (k : K) : Bd (fun n => st.e n k) := by
  have e : (fun n => st.e n k) = fun n => prob.r k + st.b n k + st.d n k - prob.Lx (st.a n) k :=
    funext fun n => (hrun n).2.2.2.2.1 k
  rw [e]
  exact (((Bd.const _).add (b_b hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)).add (b_d hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)).sub ((b_aL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).Lx prob k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_T : Bd (sT st) :=
  Bd.xs (Bd.piLp fun i => b_pstar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i) (Bd.piLp fun k => b_qstar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)
    (Bd.piLp fun k => b_tstar hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k) (Bd.piLp fun k => b_e hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem b_P : Bd (sP st) :=
  Bd.xs (b_aL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD) (Bd.piLp fun k => b_b hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k) (Bd.piLp fun k => b_d hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k) (b_estarL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)

end Bds


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section DefMain
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

/-- the main part of `t*_n` (with the lagged points replaced by current ones). -/
noncomputable def sMain (P : Problem H G) (prm : Alg34Params I K) (st : Alg34State H G) (n : ℕ) :
    XSpace H G :=
  mkX (WithLp.toLp 2 fun i =>
      (((prm.γ i (thI prm i n))⁻¹ • st.x n i - P.Q i (st.x n i))
        - ((prm.γ i (thI prm i n))⁻¹ • st.a n i - P.Q i (st.a n i)))
      + (P.R (st.a n) - P.R (st.x n)) i + P.Ladj (st.estar n - st.v n) i)
    (WithLp.toLp 2 fun k =>
      (((prm.μ k (thK prm k n))⁻¹ • st.y n k - P.Bl k (st.y n k))
        - ((prm.μ k (thK prm k n))⁻¹ • st.b n k - P.Bl k (st.b n k)))
      + (st.v n k - st.estar n k))
    (WithLp.toLp 2 fun k =>
      (((prm.ν k (thK prm k n))⁻¹ • st.z n k - P.Dl k (st.z n k))
        - ((prm.ν k (thK prm k n))⁻¹ • st.d n k - P.Dl k (st.d n k)))
      + (st.v n k - st.estar n k))
    (WithLp.toLp 2 fun k =>
      (prm.sig k (thK prm k n))⁻¹ • (st.v n k - st.estar n k) + P.Lx (st.x n - st.a n) k
        - (st.y n k - st.b n k) - (st.z n k - st.d n k))
end DefMain

section Est
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

-- lag components
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_xI (i : I) : Tz (fun n => st.x (thI prm i n) - st.x n) := (m_lagI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).pX
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_vI (i : I) : Tz (fun n => st.v (thI prm i n) - st.v n) := (m_lagI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).pV
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_xK (k : K) : Tz (fun n => st.x (thK prm k n) - st.x n) := (m_lagK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).pX
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_yK (k : K) : Tz (fun n => st.y (thK prm k n) - st.y n) := (m_lagK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).pY
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_zK (k : K) : Tz (fun n => st.z (thK prm k n) - st.z n) := (m_lagK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).pZ
include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem l_vK (k : K) : Tz (fun n => st.v (thK prm k n) - st.v n) := (m_lagK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).pV

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_errX (i : I) : Tz (fun n => st.pstar n i - pX (sMain prob prm st n) i) := by
  have e : (fun n => st.pstar n i - pX (sMain prob prm st n) i) = fun n =>
      ((prm.γ i (thI prm i n))⁻¹ • (st.x (thI prm i n) - st.x n) i
        - (prob.Q i (st.x (thI prm i n) i) - prob.Q i (st.x n i)))
      - (prob.R (st.x (thI prm i n)) - prob.R (st.x n)) i
      - prob.Ladj (st.v (thI prm i n) - st.v n) i := by
    funext n
    obtain ⟨-, e2, -⟩ := factI prob α prm JA JB JD st hrun h32.2.2.1 i n
    rw [(hrun n).2.2.2.2.2.1 i, e2]
    simp only [sMain, pX_mkX, PiLp.toLp_apply, PiLp.sub_apply, ← Ladj_sub', smul_sub]
    abel
  rw [e]
  have hgi : Bd (fun n => (prm.γ i (thI prm i n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => h31.2.2.2.2.2.2.2.2.1 i _)
  have h1 := Tz.smul_bd hgi ((l_xI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).apply i)
  have h2 : Tz (fun n => prob.Q i (st.x (thI prm i n) i) - prob.Q i (st.x n i)) :=
    ((l_xI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).apply i).mono (prob.αl i) fun n => by
      have := (hprob.1 i).2.2.2.2.2 (st.x (thI prm i n) i) (st.x n i)
      simpa using this
  have h3 : Tz (fun n => (prob.R (st.x (thI prm i n)) - prob.R (st.x n)) i) :=
    (l_xI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).mono prob.χ fun n =>
      (PiLp.norm_apply_le _ i).trans (hprob.2.2.2.2.2 _ _)
  exact ((h1.sub h2).sub h3).sub ((l_vI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).Ladj prob i)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_errY (k : K) : Tz (fun n => st.qstar n k - pY (sMain prob prm st n) k) := by
  have e : (fun n => st.qstar n k - pY (sMain prob prm st n) k) = fun n =>
      ((prm.μ k (thK prm k n))⁻¹ • (st.y (thK prm k n) - st.y n) k
        - (prob.Bl k (st.y (thK prm k n) k) - prob.Bl k (st.y n k)))
      + (st.v (thK prm k n) - st.v n) k := by
    funext n
    rw [(factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.2.1]
    simp only [sMain, pY_mkX, PiLp.toLp_apply, PiLp.sub_apply, smul_sub]
    abel
  rw [e]
  have hgi : Bd (fun n => (prm.μ k (thK prm k n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).1)
  have h1 := Tz.smul_bd hgi ((l_yK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)
  have h2 : Tz (fun n => prob.Bl k (st.y (thK prm k n) k) - prob.Bl k (st.y n k)) :=
    ((l_yK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k).mono (prob.βl k) fun n => by
      have := (hprob.2.1 k).2.2.2.2.2 (st.y (thK prm k n) k) (st.y n k)
      simpa using this
  exact (h1.sub h2).add ((l_vK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_errZ (k : K) : Tz (fun n => st.tstar n k - pZ (sMain prob prm st n) k) := by
  have e : (fun n => st.tstar n k - pZ (sMain prob prm st n) k) = fun n =>
      ((prm.ν k (thK prm k n))⁻¹ • (st.z (thK prm k n) - st.z n) k
        - (prob.Dl k (st.z (thK prm k n) k) - prob.Dl k (st.z n k)))
      + (st.v (thK prm k n) - st.v n) k := by
    funext n
    rw [(factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.2.2.1]
    simp only [sMain, pZ_mkX, PiLp.toLp_apply, PiLp.sub_apply, smul_sub]
    abel
  rw [e]
  have hgi : Bd (fun n => (prm.ν k (thK prm k n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.1)
  have h1 := Tz.smul_bd hgi ((l_zK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)
  have h2 : Tz (fun n => prob.Dl k (st.z (thK prm k n) k) - prob.Dl k (st.z n k)) :=
    ((l_zK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k).mono (prob.δl k) fun n => by
      have := (hprob.2.2.1 k).2.2.2.2.2 (st.z (thK prm k n) k) (st.z n k)
      simpa using this
  exact (h1.sub h2).add ((l_vK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_errV (k : K) : Tz (fun n => st.e n k - pV (sMain prob prm st n) k) := by
  have e : (fun n => st.e n k - pV (sMain prob prm st n) k) = fun n =>
      (prm.sig k (thK prm k n))⁻¹ • (st.v (thK prm k n) - st.v n) k
      + prob.Lx (st.x (thK prm k n) - st.x n) k
      - (st.y (thK prm k n) - st.y n) k - (st.z (thK prm k n) - st.z n) k := by
    funext n
    have hs : 0 < prm.sig k (thK prm k n) :=
      lt_of_lt_of_le (m_eps h31) (h31.2.2.2.2.2.2.2.2.2 k _).2.2.1
    have hes := (factK prob α prm JA JB JD st hrun h32.2.2.2.1 k n).2.2.1
    have hr : prob.r k = prob.Lx (st.x (thK prm k n)) k - st.y (thK prm k n) k
        - st.z (thK prm k n) k
        - (prm.sig k (thK prm k n))⁻¹ • (st.estar n k - st.v (thK prm k n) k) := by
      rw [hes, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
      abel
    rw [(hrun n).2.2.2.2.1 k, hr]
    simp only [sMain, pV_mkX, PiLp.toLp_apply, PiLp.sub_apply, ← Lx_sub']
    module
  rw [e]
  have hsi : Bd (fun n => (prm.sig k (thK prm k n))⁻¹) :=
    Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.2)
  exact (((Tz.smul_bd hsi ((l_vK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)).add ((l_xK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).Lx prob k)).sub
    ((l_yK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)).sub ((l_zK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_err : Tz (fun n => sT st n - sMain prob prm st n) :=
  Tz.xs (Tz.piLp fun i => by simpa [sT] using e_errX hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i)
    (Tz.piLp fun k => by simpa [sT] using e_errY hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)
    (Tz.piLp fun k => by simpa [sT] using e_errZ hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)
    (Tz.piLp fun k => by simpa [sT] using e_errV hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k)

end Est


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Est2
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_lower (n : ℕ) :
    σ * (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)
      + ε * ‖st.v n - st.estar n‖ ^ 2 ≤ ⟪sX st n - sP st n, sMain prob prm st n⟫_ℝ := by
  obtain ⟨-, hσ0, hε0, -, -, -, -, -, hγ, hμν⟩ := h31
  rw [xs_inner]
  simp only [sX, sP, sMain, pX_sub, pY_sub, pZ_sub, pV_sub, pX_mkX, pY_mkX, pZ_mkX, pV_mkX,
    PiLp.toLp_apply, PiLp.sub_apply]
  -- x-block
  have hX : ∑ i, ⟪st.x n i - st.a n i, (((prm.γ i (thI prm i n))⁻¹ • st.x n i
        - prob.Q i (st.x n i)) - ((prm.γ i (thI prm i n))⁻¹ • st.a n i - prob.Q i (st.a n i)))
        + (prob.R (st.a n) i - prob.R (st.x n) i) + prob.Ladj (st.estar n - st.v n) i⟫_ℝ
      = ∑ i, ⟪st.x n i - st.a n i, ((prm.γ i (thI prm i n))⁻¹ • st.x n i
        - prob.Q i (st.x n i)) - ((prm.γ i (thI prm i n))⁻¹ • st.a n i - prob.Q i (st.a n i))⟫_ℝ
      + ∑ i, ⟪st.x n i - st.a n i, prob.R (st.a n) i - prob.R (st.x n) i⟫_ℝ
      + ∑ i, ⟪st.x n i - st.a n i, prob.Ladj (st.estar n - st.v n) i⟫_ℝ := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_add_right, inner_add_right]
  have hY : ∑ k, ⟪st.y n k - st.b n k, (((prm.μ k (thK prm k n))⁻¹ • st.y n k
        - prob.Bl k (st.y n k)) - ((prm.μ k (thK prm k n))⁻¹ • st.b n k - prob.Bl k (st.b n k)))
        + (st.v n k - st.estar n k)⟫_ℝ
      = ∑ k, ⟪st.y n k - st.b n k, ((prm.μ k (thK prm k n))⁻¹ • st.y n k
        - prob.Bl k (st.y n k)) - ((prm.μ k (thK prm k n))⁻¹ • st.b n k - prob.Bl k (st.b n k))⟫_ℝ
      + ∑ k, ⟪st.y n k - st.b n k, st.v n k - st.estar n k⟫_ℝ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_right]
  have hZ : ∑ k, ⟪st.z n k - st.d n k, (((prm.ν k (thK prm k n))⁻¹ • st.z n k
        - prob.Dl k (st.z n k)) - ((prm.ν k (thK prm k n))⁻¹ • st.d n k - prob.Dl k (st.d n k)))
        + (st.v n k - st.estar n k)⟫_ℝ
      = ∑ k, ⟪st.z n k - st.d n k, ((prm.ν k (thK prm k n))⁻¹ • st.z n k
        - prob.Dl k (st.z n k)) - ((prm.ν k (thK prm k n))⁻¹ • st.d n k - prob.Dl k (st.d n k))⟫_ℝ
      + ∑ k, ⟪st.z n k - st.d n k, st.v n k - st.estar n k⟫_ℝ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_right]
  have hV : ∑ k, ⟪st.v n k - st.estar n k, (prm.sig k (thK prm k n))⁻¹ •
        (st.v n k - st.estar n k) + prob.Lx (st.x n - st.a n) k
        - (st.y n k - st.b n k) - (st.z n k - st.d n k)⟫_ℝ
      = ∑ k, (prm.sig k (thK prm k n))⁻¹ * ‖st.v n k - st.estar n k‖ ^ 2
      + ∑ k, ⟪st.v n k - st.estar n k, prob.Lx (st.x n - st.a n) k⟫_ℝ
      - ∑ k, ⟪st.y n k - st.b n k, st.v n k - st.estar n k⟫_ℝ
      - ∑ k, ⟪st.z n k - st.d n k, st.v n k - st.estar n k⟫_ℝ := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sub_right, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm (st.y n k - st.b n k),
      real_inner_comm (st.z n k - st.d n k)]
  rw [hX, hY, hZ, hV]
  -- the skew coupling
  have hsk := Ladj_skew' prob (st.x n - st.a n) (st.estar n - st.v n)
  simp only [PiLp.sub_apply] at hsk
  have hsk2 : ∑ k, ⟪st.estar n k - st.v n k, prob.Lx (st.x n - st.a n) k⟫_ℝ
      = -∑ k, ⟪st.v n k - st.estar n k, prob.Lx (st.x n - st.a n) k⟫_ℝ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← inner_neg_left, neg_sub]
  -- strong monotonicity (Lemma A.2)
  have hE : ∀ i, (prob.χ + σ) * ‖st.x n i - st.a n i‖ ^ 2 ≤ ⟪st.x n i - st.a n i,
      ((prm.γ i (thI prm i n))⁻¹ • st.x n i - prob.Q i (st.x n i))
        - ((prm.γ i (thI prm i n))⁻¹ • st.a n i - prob.Q i (st.a n i))⟫_ℝ := by
    intro i
    have hg := hγ i (thI prm i n)
    refine lemma_A_2 (prob.αl i) (hprob.1 i).2.2.2.2.1 (prob.Q i) (hprob.1 i).2.2.2.2.2
      (prob.χ + σ) (by linarith [hprob.2.2.2.2.1]) (prm.γ i (thI prm i n))
      ⟨lt_of_lt_of_le hε0 hg.1, by rw [← add_assoc]; exact hg.2⟩ (st.x n i) (st.a n i)
  have hF : ∀ k, σ * ‖st.y n k - st.b n k‖ ^ 2 ≤ ⟪st.y n k - st.b n k,
      ((prm.μ k (thK prm k n))⁻¹ • st.y n k - prob.Bl k (st.y n k))
        - ((prm.μ k (thK prm k n))⁻¹ • st.b n k - prob.Bl k (st.b n k))⟫_ℝ := by
    intro k
    have hg := (hμν k (thK prm k n)).1
    exact lemma_A_2 (prob.βl k) (hprob.2.1 k).2.2.2.2.1 (prob.Bl k) (hprob.2.1 k).2.2.2.2.2
      σ hσ0 (prm.μ k (thK prm k n)) ⟨lt_of_lt_of_le hε0 hg.1, hg.2⟩ (st.y n k) (st.b n k)
  have hG : ∀ k, σ * ‖st.z n k - st.d n k‖ ^ 2 ≤ ⟪st.z n k - st.d n k,
      ((prm.ν k (thK prm k n))⁻¹ • st.z n k - prob.Dl k (st.z n k))
        - ((prm.ν k (thK prm k n))⁻¹ • st.d n k - prob.Dl k (st.d n k))⟫_ℝ := by
    intro k
    have hg := (hμν k (thK prm k n)).2.1
    exact lemma_A_2 (prob.δl k) (hprob.2.2.1 k).2.2.2.2.1 (prob.Dl k) (hprob.2.2.1 k).2.2.2.2.2
      σ hσ0 (prm.ν k (thK prm k n)) ⟨lt_of_lt_of_le hε0 hg.1, hg.2⟩ (st.z n k) (st.d n k)
  have hS : ∀ k, ε * ‖st.v n k - st.estar n k‖ ^ 2 ≤
      (prm.sig k (thK prm k n))⁻¹ * ‖st.v n k - st.estar n k‖ ^ 2 := by
    intro k
    have hg := (hμν k (thK prm k n)).2.2
    have hs0 : 0 < prm.sig k (thK prm k n) := lt_of_lt_of_le hε0 hg.1
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [le_inv_comm₀ hε0 hs0]; simpa [one_div] using hg.2
  -- the `R` term
  have hR : -(prob.χ * ‖st.x n - st.a n‖ ^ 2) ≤
      ∑ i, ⟪st.x n i - st.a n i, prob.R (st.a n) i - prob.R (st.x n) i⟫_ℝ := by
    have e : ∑ i, ⟪st.x n i - st.a n i, prob.R (st.a n) i - prob.R (st.x n) i⟫_ℝ
        = ⟪st.x n - st.a n, prob.R (st.a n) - prob.R (st.x n)⟫_ℝ := by
      rw [PiLp.inner_apply]; simp only [PiLp.sub_apply]
    rw [e]
    have h1 := real_inner_le_norm (st.x n - st.a n) (prob.R (st.x n) - prob.R (st.a n))
    have h2 := hprob.2.2.2.2.2 (st.x n) (st.a n)
    have h3 : ⟪st.x n - st.a n, prob.R (st.a n) - prob.R (st.x n)⟫_ℝ
        = -⟪st.x n - st.a n, prob.R (st.x n) - prob.R (st.a n)⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    rw [h3]
    have h4 : ‖st.x n - st.a n‖ * ‖prob.R (st.x n) - prob.R (st.a n)‖
        ≤ ‖st.x n - st.a n‖ * (prob.χ * ‖st.x n - st.a n‖) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    nlinarith
  have hnx : ‖st.x n - st.a n‖ ^ 2 = ∑ i, ‖st.x n i - st.a n i‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp only [PiLp.sub_apply]
  have hny : ‖st.y n - st.b n‖ ^ 2 = ∑ k, ‖st.y n k - st.b n k‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp only [PiLp.sub_apply]
  have hnz : ‖st.z n - st.d n‖ ^ 2 = ∑ k, ‖st.z n k - st.d n k‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp only [PiLp.sub_apply]
  have hnv : ‖st.v n - st.estar n‖ ^ 2 = ∑ k, ‖st.v n k - st.estar n k‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp only [PiLp.sub_apply]
  have sE := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hE i
  have sF := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hF k
  have sG := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hG k
  have sS := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hS k
  rw [← Finset.mul_sum] at sE sF sG sS
  rw [hnx, hny, hnz, hnv]
  rw [hnx] at hR
  nlinarith

end Est2


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Est3

theorem sq_to {E : Type*} [NormedAddCommGroup E] (u : ℕ → E)
    (h : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 0)) : Tz u := by
  rw [Tz.iff_norm]
  have := h.sqrt
  rw [Real.sqrt_zero] at this
  exact this.congr fun n => Real.sqrt_sq (norm_nonneg _)
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_o1 : Tendsto (fun n => ⟪sX st n - sP st n, sT st n - sMain prob prm st n⟫_ℝ) atTop
    (𝓝 0) :=
  Tz.inner_bd ((m_bdX hprob h31 h32 hlam hJA hJB hJD hrun hD).sub (b_P hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)) (e_err hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_qdiff : Tz (fun n => mkX (st.x n) (st.y n) (st.z n) (st.estar n) - sQ prm st n) := by
  apply Tz.xs
  · refine Tz.piLp fun i => ?_
    have := ((l_xI hprob h31 h32 h33 hlam hJA hJB hJD hrun hD i).apply i).neg
    simpa [sQ] using this
  · refine Tz.piLp fun k => ?_
    have := ((l_yK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k).neg
    simpa [sQ] using this
  · refine Tz.piLp fun k => ?_
    have := ((l_zK hprob h31 h32 h33 hlam hJA hJB hJD hrun hD k).apply k).neg
    simpa [sQ] using this
  · simpa [sQ] using (Tz.zero : Tz (fun _ : ℕ => (0 : PiLp 2 G)))

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_o2 : Tendsto (fun n => ‖sP st n - sQ prm st n‖ ^ 2
    - (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)) atTop (𝓝 0) := by
  set U : ℕ → XSpace H G := fun n => sP st n - mkX (st.x n) (st.y n) (st.z n) (st.estar n)
  set W : ℕ → XSpace H G := fun n => mkX (st.x n) (st.y n) (st.z n) (st.estar n) - sQ prm st n
  have hU : Bd U := (b_P hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).sub (Bd.xs (b_x hprob h31 h32 h33 hlam hJA hJB hJD hrun hD) (b_y hprob h31 h32 h33 hlam hJA hJB hJD hrun hD) (b_z hprob h31 h32 h33 hlam hJA hJB hJD hrun hD) (b_estarL hprob h31 h32 h33 hlam hJA hJB hJD hrun hD))
  have hW : Tz W := e_qdiff hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have hnU : ∀ n, ‖U n‖ ^ 2 = ‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2
      + ‖st.z n - st.d n‖ ^ 2 := by
    intro n
    rw [xs_normsq4]
    simp only [U, sP, pX_sub, pY_sub, pZ_sub, pV_sub, pX_mkX, pY_mkX, pZ_mkX, pV_mkX, sub_self,
      norm_zero]
    rw [norm_sub_rev (st.a n), norm_sub_rev (st.b n), norm_sub_rev (st.d n)]
    ring
  have e : ∀ n, ‖sP st n - sQ prm st n‖ ^ 2
      - (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)
      = 2 * ⟪U n, W n⟫_ℝ + ‖W n‖ ^ 2 := by
    intro n
    rw [← hnU]
    have : sP st n - sQ prm st n = U n + W n := by simp only [U, W]; abel
    rw [this, norm_add_sq_real]; ring
  simp only [e]
  have h1 := (Tz.inner_bd hU hW).const_mul 2
  have h2 := (Tz.iff_norm.1 hW).pow 2
  simpa using h1.add h2

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_phi : Tendsto (fun n =>
    (σ - (4 * α)⁻¹) * (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)
      + ε * ‖st.v n - st.estar n‖ ^ 2) atTop (𝓝 0) := by
  have hα0 := m_alpha hprob h31
  have hε0 := m_eps h31
  have hσα : (4 * α)⁻¹ < σ := by have := h31.2.2.2.2.1; rwa [one_div] at this
  have hiii := (m_p26 hprob h31 h32 hlam hJA hJB hJD hrun hD).2.2.1 (b_T hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).isBounded
  have ho1 := e_o1 hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have ho2 := (e_o2 hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).const_mul (4 * α)⁻¹
  rw [mul_zero] at ho2
  set Φ := fun n =>
    (σ - (4 * α)⁻¹) * (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)
      + ε * ‖st.v n - st.estar n‖ ^ 2
  have hΦ0 : ∀ n, 0 ≤ Φ n := fun n => by
    have : 0 ≤ σ - (4 * α)⁻¹ := by linarith
    simp only [Φ]; positivity
  have hΦle : ∀ n, Φ n ≤ st.Δ n - ⟪sX st n - sP st n, sT st n - sMain prob prm st n⟫_ℝ
      + (4 * α)⁻¹ * (‖sP st n - sQ prm st n‖ ^ 2
        - (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2)) := by
    intro n
    have hl := e_lower hprob h31 h32 h33 hlam hJA hJB hJD hrun hD n
    have hΔ := (m_run h31 h32 hlam hJA hJB hJD hrun n).2.2.1
    have hsplit : ⟪sX st n - sP st n, sT st n⟫_ℝ = ⟪sX st n - sP st n, sMain prob prm st n⟫_ℝ
        + ⟪sX st n - sP st n, sT st n - sMain prob prm st n⟫_ℝ := by
      rw [← inner_add_right, add_sub_cancel]
    simp only [Φ]
    rw [hΔ, hsplit]
    nlinarith
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hΦ0 n), fun b hb => ?_⟩
  have hb4 : 0 < b / 4 := by positivity
  filter_upwards [hiii (b / 4) hb4, ho1.eventually (Metric.ball_mem_nhds 0 hb4),
    ho2.eventually (Metric.ball_mem_nhds 0 hb4)] with n h1 h2 h3
  rw [Real.dist_eq, sub_zero] at h2 h3
  have := hΦle n
  have := abs_lt.1 h2
  have := abs_lt.1 h3
  linarith

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem e_limits : Tz (fun n => st.x n - st.a n) ∧ Tz (fun n => st.y n - st.b n) ∧
    Tz (fun n => st.z n - st.d n) ∧ Tz (fun n => st.v n - st.estar n) := by
  have hφ := e_phi hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have hα0 := m_alpha hprob h31
  have hε0 := m_eps h31
  have hσα : (4 * α)⁻¹ < σ := by have := h31.2.2.2.2.1; rwa [one_div] at this
  set c := σ - (4 * α)⁻¹
  have hc : 0 < c := by simp only [c]; linarith
  have key : ∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) → ∀ (C : ℝ), 0 < C →
      (∀ n, C * f n ≤ (σ - (4 * α)⁻¹) * (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2
        + ‖st.z n - st.d n‖ ^ 2) + ε * ‖st.v n - st.estar n‖ ^ 2) →
      Tendsto f atTop (𝓝 0) := by
    intro f hf C hC hle
    have h2 := hφ.const_mul C⁻¹
    rw [mul_zero] at h2
    refine squeeze_zero hf (fun n => ?_) h2
    rw [le_inv_mul_iff₀ hC]; exact hle n
  have hS0 : ∀ n, 0 ≤ ‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2 + ‖st.z n - st.d n‖ ^ 2 :=
    fun n => by positivity
  have hA : ∀ n, 0 ≤ c * ‖st.x n - st.a n‖ ^ 2 := fun n => by positivity
  have hB : ∀ n, 0 ≤ c * ‖st.y n - st.b n‖ ^ 2 := fun n => by positivity
  have hC : ∀ n, 0 ≤ c * ‖st.z n - st.d n‖ ^ 2 := fun n => by positivity
  have hV : ∀ n, 0 ≤ ε * ‖st.v n - st.estar n‖ ^ 2 := fun n => by positivity
  have hexp : ∀ n, (σ - (4 * α)⁻¹) * (‖st.x n - st.a n‖ ^ 2 + ‖st.y n - st.b n‖ ^ 2
      + ‖st.z n - st.d n‖ ^ 2) + ε * ‖st.v n - st.estar n‖ ^ 2
      = c * ‖st.x n - st.a n‖ ^ 2 + c * ‖st.y n - st.b n‖ ^ 2 + c * ‖st.z n - st.d n‖ ^ 2
        + ε * ‖st.v n - st.estar n‖ ^ 2 := fun n => by simp only [c]; ring
  refine ⟨sq_to _ ?_, sq_to _ ?_, sq_to _ ?_, sq_to _ ?_⟩
  · exact key _ (fun n => sq_nonneg _) c hc fun n => by
      rw [hexp]; linarith [hB n, hC n, hV n]
  · exact key _ (fun n => sq_nonneg _) c hc fun n => by
      rw [hexp]; linarith [hA n, hC n, hV n]
  · exact key _ (fun n => sq_nonneg _) c hc fun n => by
      rw [hexp]; linarith [hA n, hB n, hV n]
  · exact key _ (fun n => sq_nonneg _) ε hε0 fun n => by
      rw [hexp]; linarith [hA n, hB n, hC n]

end Est3


open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

section Emb
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]

theorem pi_inner_single {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ j, NormedAddCommGroup (β j)] [∀ j, InnerProductSpace ℝ (β j)]
    (f : PiLp 2 β) (i : ι) (h : β i) :
    ⟪f, WithLp.toLp 2 (Pi.single i h)⟫_ℝ = ⟪f i, h⟫_ℝ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem inner_eX (X : XSpace H G) (i : I) (h : H i) :
    ⟪X, mkX (WithLp.toLp 2 (Pi.single i h)) 0 0 0⟫_ℝ = ⟪pX X i, h⟫_ℝ := by
  rw [xs_inner4]
  simp only [pX_mkX, pY_mkX, pZ_mkX, pV_mkX, inner_zero_right, add_zero]
  exact pi_inner_single _ _ _

theorem inner_eV (X : XSpace H G) (k : K) (h : G k) :
    ⟪X, mkX 0 0 0 (WithLp.toLp 2 (Pi.single k h))⟫_ℝ = ⟪pV X k, h⟫_ℝ := by
  rw [xs_inner4]
  simp only [pX_mkX, pY_mkX, pZ_mkX, pV_mkX, inner_zero_right, zero_add]
  exact pi_inner_single _ _ _
end Emb

section Final
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    {prob : Problem H G} (hprob : prob.Hyp)
    {α σ ε : ℝ} {prm : Alg34Params I K} (h31 : Assumption31 prob α σ ε prm)
    {Pw : ℕ} (h32 : Assumption32 Pw prm) {T : ℕ} (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    {JA : ∀ i, ℝ → H i → H i} {JB JD : ∀ k, ℝ → G k → G k}
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    {st : Alg34State H G} (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_main0 : Tz (sMain prob prm st) := by
  obtain ⟨hdx, hdy, hdz, hdv⟩ := e_limits hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  apply Tz.xs
  · refine Tz.piLp fun i => ?_
    have e : (fun n => pX (sMain prob prm st n) i) = fun n =>
        ((prm.γ i (thI prm i n))⁻¹ • (st.x n - st.a n) i
          - (prob.Q i (st.x n i) - prob.Q i (st.a n i)))
        + (prob.R (st.a n) - prob.R (st.x n)) i + prob.Ladj (-(st.v n - st.estar n)) i := by
      funext n; simp only [sMain, pX_mkX, PiLp.toLp_apply, PiLp.sub_apply, smul_sub, neg_sub]
      abel
    rw [e]
    have hgi : Bd (fun n => (prm.γ i (thI prm i n))⁻¹) :=
      Bd.inv_of_Icc (m_eps h31) (fun n => h31.2.2.2.2.2.2.2.2.1 i _)
    have h1 := Tz.smul_bd hgi (hdx.apply i)
    have h2 : Tz (fun n => prob.Q i (st.x n i) - prob.Q i (st.a n i)) :=
      (hdx.apply i).mono (prob.αl i) fun n => by
        have := (hprob.1 i).2.2.2.2.2 (st.x n i) (st.a n i); simpa using this
    have h3 : Tz (fun n => (prob.R (st.a n) - prob.R (st.x n)) i) :=
      hdx.mono prob.χ fun n => (PiLp.norm_apply_le _ i).trans (by
        rw [norm_sub_rev (st.x n)]; exact hprob.2.2.2.2.2 _ _)
    exact ((h1.sub h2).add h3).add (hdv.neg.Ladj prob i)
  · refine Tz.piLp fun k => ?_
    have e : (fun n => pY (sMain prob prm st n) k) = fun n =>
        ((prm.μ k (thK prm k n))⁻¹ • (st.y n - st.b n) k
          - (prob.Bl k (st.y n k) - prob.Bl k (st.b n k))) + (st.v n - st.estar n) k := by
      funext n; simp only [sMain, pY_mkX, PiLp.toLp_apply, PiLp.sub_apply, smul_sub]; abel
    rw [e]
    have hgi : Bd (fun n => (prm.μ k (thK prm k n))⁻¹) :=
      Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).1)
    have h2 : Tz (fun n => prob.Bl k (st.y n k) - prob.Bl k (st.b n k)) :=
      (hdy.apply k).mono (prob.βl k) fun n => by
        have := (hprob.2.1 k).2.2.2.2.2 (st.y n k) (st.b n k); simpa using this
    exact ((Tz.smul_bd hgi (hdy.apply k)).sub h2).add (hdv.apply k)
  · refine Tz.piLp fun k => ?_
    have e : (fun n => pZ (sMain prob prm st n) k) = fun n =>
        ((prm.ν k (thK prm k n))⁻¹ • (st.z n - st.d n) k
          - (prob.Dl k (st.z n k) - prob.Dl k (st.d n k))) + (st.v n - st.estar n) k := by
      funext n; simp only [sMain, pZ_mkX, PiLp.toLp_apply, PiLp.sub_apply, smul_sub]; abel
    rw [e]
    have hgi : Bd (fun n => (prm.ν k (thK prm k n))⁻¹) :=
      Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.1)
    have h2 : Tz (fun n => prob.Dl k (st.z n k) - prob.Dl k (st.d n k)) :=
      (hdz.apply k).mono (prob.δl k) fun n => by
        have := (hprob.2.2.1 k).2.2.2.2.2 (st.z n k) (st.d n k); simpa using this
    exact ((Tz.smul_bd hgi (hdz.apply k)).sub h2).add (hdv.apply k)
  · refine Tz.piLp fun k => ?_
    have e : (fun n => pV (sMain prob prm st n) k) = fun n =>
        (prm.sig k (thK prm k n))⁻¹ • (st.v n - st.estar n) k + prob.Lx (st.x n - st.a n) k
          - (st.y n - st.b n) k - (st.z n - st.d n) k := by
      funext n; simp only [sMain, pV_mkX, PiLp.toLp_apply, PiLp.sub_apply]
    rw [e]
    have hsi : Bd (fun n => (prm.sig k (thK prm k n))⁻¹) :=
      Bd.inv_of_Icc (m_eps h31) (fun n => (h31.2.2.2.2.2.2.2.2.2 k _).2.2)
    exact (((Tz.smul_bd hsi (hdv.apply k)).add (hdx.Lx prob k)).sub (hdy.apply k)).sub
      (hdz.apply k)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_XP : Tz (fun n => sX st n - sP st n) := by
  obtain ⟨hdx, hdy, hdz, hdv⟩ := e_limits hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  exact Tz.xs (by simpa [sX, sP] using hdx) (by simpa [sX, sP] using hdy)
    (by simpa [sX, sP] using hdz) (by simpa [sX, sP] using hdv)

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_PQ : Tz (fun n => sP st n - sQ prm st n) := by
  obtain ⟨hdx, hdy, hdz, hdv⟩ := e_limits hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have h1 := (f_XP hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).neg
  have h2 : Tz (fun n => sX st n - mkX (st.x n) (st.y n) (st.z n) (st.estar n)) := by
    apply Tz.xs
    · simpa [sX] using (Tz.zero : Tz (fun _ : ℕ => (0 : PiLp 2 H)))
    · simpa [sX] using (Tz.zero : Tz (fun _ : ℕ => (0 : PiLp 2 G)))
    · simpa [sX] using (Tz.zero : Tz (fun _ : ℕ => (0 : PiLp 2 G)))
    · simpa [sX] using hdv
  have h3 := e_qdiff hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have := (h1.add h2).add h3
  refine this.congr' (Eventually.of_forall fun n => ?_)
  simp only; abel

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_T : Tz (sT st) := by
  have := (e_err hprob h31 h32 h33 hlam hJA hJB hJD hrun hD).add (f_main0 hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)
  refine this.congr' (Eventually.of_forall fun n => ?_)
  simp only [sub_add_cancel]

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_weak : ∃ z ∈ zer (saddleOp prob), WeakTendsto (sX st) z := by
  have hiv := (m_p26 hprob h31 h32 hlam hJA hJB hJD hrun hD).2.2.2
  refine hiv (fun y => ?_) (f_PQ hprob h31 h32 h33 hlam hJA hJB hJD hrun hD) (f_T hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)
  have := Tz.inner_bd (Bd.const y) (f_XP hprob h31 h32 h33 hlam hJA hJB hJD hrun hD)
  rw [inner_zero_left]
  refine this.congr fun n => real_inner_comm _ _

include hprob h31 h32 h33 hlam hJA hJB hJD hrun hD in
theorem f_all :
    (∀ i, Summable fun n => ‖st.x (n + 1) i - st.x n i‖ ^ 2) ∧
    (∀ k, Summable (fun n => ‖st.y (n + 1) k - st.y n k‖ ^ 2) ∧
      Summable (fun n => ‖st.z (n + 1) k - st.z n k‖ ^ 2) ∧
      Summable (fun n => ‖st.v (n + 1) k - st.v n k‖ ^ 2)) ∧
    (∀ i, Tendsto (fun n => st.x n i - st.a n i) atTop (𝓝 0)) ∧
    (∀ k, Tendsto (fun n => st.y n k - st.b n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.z n k - st.d n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.v n k - st.estar n k) atTop (𝓝 0)) ∧
    ∃ xbar ∈ primalSet prob, ∃ vbar ∈ dualSet prob, (xbar, vbar) ∈ ktSet prob ∧
      (∀ i, WeakTendsto (fun n => st.x n i) (xbar i) ∧ WeakTendsto (fun n => st.a n i) (xbar i)) ∧
      ∀ k, WeakTendsto (fun n => st.v n k) (vbar k) := by
  have hS := m_summ hprob h31 h32 hlam hJA hJB hJD hrun hD
  obtain ⟨hdx, hdy, hdz, hdv⟩ := e_limits hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
  have sm : ∀ (f : ℕ → ℝ), (∀ n, f n ≤ ‖sX st (n + 1) - sX st n‖) →
      Summable (fun n => f n ^ 2) → True := fun _ _ _ => trivial
  have hsum : ∀ (g : ℕ → ℝ), (∀ n, 0 ≤ g n) → (∀ n, g n ≤ ‖sX st (n + 1) - sX st n‖) →
      Summable (fun n => g n ^ 2) := fun g h0 hle =>
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => pow_le_pow_left₀ (h0 n) (hle n) 2) hS
  refine ⟨fun i => ?_, fun k => ⟨?_, ?_, ?_⟩, fun i => ?_, fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hsum _ (fun n => norm_nonneg _) fun n => by
      have := norm_pXi_le (sX st (n + 1) - sX st n) i; simpa [sX] using this
  · exact hsum _ (fun n => norm_nonneg _) fun n => by
      have := norm_pYk_le (sX st (n + 1) - sX st n) k; simpa [sX] using this
  · exact hsum _ (fun n => norm_nonneg _) fun n => by
      have := norm_pZk_le (sX st (n + 1) - sX st n) k; simpa [sX] using this
  · exact hsum _ (fun n => norm_nonneg _) fun n => by
      have := norm_pVk_le (sX st (n + 1) - sX st n) k; simpa [sX] using this
  · have := hdx.apply i; simpa [Tz] using this
  · have := hdy.apply k; simpa [Tz] using this
  · have := hdz.apply k; simpa [Tz] using this
  · have := hdv.apply k; simpa [Tz] using this
  · obtain ⟨Zb, hZb, hw⟩ := f_weak hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
    have hkt := (proposition_2_2_iii_iv prob hprob).1 Zb hZb
    have hPD := (proposition_2_2_iii_iv prob hprob).2.1 hkt
    refine ⟨pX Zb, hPD.1, pV Zb, hPD.2, hkt, fun i => ⟨?_, ?_⟩, fun k => ?_⟩
    · intro h
      have := hw (mkX (WithLp.toLp 2 (Pi.single i h)) 0 0 0)
      simp only [inner_eX] at this
      simpa [sX] using this
    · intro h
      have h1 := hw (mkX (WithLp.toLp 2 (Pi.single i h)) 0 0 0)
      simp only [inner_eX] at h1
      have h2 := Tz.inner_bd (Bd.const h) (hdx.apply i)
      have h3 := h1.sub h2
      simp only [sub_zero] at h3
      refine h3.congr fun n => ?_
      simp only [sX, pX_mkX, PiLp.sub_apply]
      rw [real_inner_comm (st.x n i - st.a n i) h, ← inner_sub_left, sub_sub_cancel]
    · intro h
      have := hw (mkX 0 0 0 (WithLp.toLp 2 (Pi.single k h)))
      simp only [inner_eV] at this
      simpa [sX] using this

end Final


theorem solution {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp)
    (α σ ε : ℝ) (prm : Alg34Params I K) (h31 : Assumption31 prob α σ ε prm)
    (Pw : ℕ) (h32 : Assumption32 Pw prm) (T : ℕ) (h33 : Assumption33 T prm)
    (hlam : ∀ n, prm.lam n ∈ Set.Icc ε (2 - ε))
    (JA : ∀ i, ℝ → H i → H i) (JB JD : ∀ k, ℝ → G k → G k)
    (hJA : ∀ i (γ : ℝ), 0 < γ → IsResolvent γ (prob.A i) (JA i γ))
    (hJB : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Bm k) (JB k γ))
    (hJD : ∀ k (γ : ℝ), 0 < γ → IsResolvent γ (prob.Dm k) (JD k γ))
    (st : Alg34State H G) (hrun : IsAlg34Run prob α prm JA JB JD st)
    (hD : (dualSet prob).Nonempty) :
    (∀ i, Summable fun n => ‖st.x (n + 1) i - st.x n i‖ ^ 2) ∧
    (∀ k, Summable (fun n => ‖st.y (n + 1) k - st.y n k‖ ^ 2) ∧
      Summable (fun n => ‖st.z (n + 1) k - st.z n k‖ ^ 2) ∧
      Summable (fun n => ‖st.v (n + 1) k - st.v n k‖ ^ 2)) ∧
    (∀ i, Tendsto (fun n => st.x n i - st.a n i) atTop (𝓝 0)) ∧
    (∀ k, Tendsto (fun n => st.y n k - st.b n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.z n k - st.d n k) atTop (𝓝 0) ∧
      Tendsto (fun n => st.v n k - st.estar n k) atTop (𝓝 0)) ∧
    ∃ xbar ∈ primalSet prob, ∃ vbar ∈ dualSet prob, (xbar, vbar) ∈ ktSet prob ∧
      (∀ i, WeakTendsto (fun n => st.x n i) (xbar i) ∧ WeakTendsto (fun n => st.a n i) (xbar i)) ∧
      ∀ k, WeakTendsto (fun n => st.v n k) (vbar k) :=
  f_all hprob h31 h32 h33 hlam hJA hJB hJD hrun hD
