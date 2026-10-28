-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P04.linear_bsc_css_conversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:12:07.290574+00:00
-- url     : https://prove2.me/submissions/c5d3b98f-88ff-4d47-b8c4-b26fb4e71695

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

end QAlgorithms.Papers.Independent.Support50.P04

namespace A3S54P04
open QAlgorithms.Papers.Independent.Support50.P04

@[simp] lemma v0 : (0 : ZMod 2).val = 0 := rfl
@[simp] lemma v1 : (1 : ZMod 2).val = 1 := rfl
@[simp] lemma one_one : (1 + 1 : ZMod 2) = 0 := rfl
@[simp] lemma zo : (0 : ZMod 2) ≠ 1 := by decide
@[simp] lemma oz : (1 : ZMod 2) ≠ 0 := by decide

lemma z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

def f (a : ZMod 2) (t : Fin 2) : ℂ := (-1 : ℂ) ^ (a.val * t.val)

lemma f_add (a b : ZMod 2) (t : Fin 2) : f (a + b) t = f a t * f b t := by
  rcases z2 a with rfl | rfl <;> rcases z2 b with rfl | rfl <;> fin_cases t <;> simp [f]

lemma f_sum_left (a b : ZMod 2) : ∑ t : Fin 2, f a t * f b t = if a = b then 2 else 0 := by
  rcases z2 a with rfl | rfl <;> rcases z2 b with rfl | rfl <;> simp [f, Fin.sum_univ_two] <;> norm_num

lemma f_sum_right (t t' : Fin 2) : ∑ a : ZMod 2, f a t * f a t' = if t = t' then 2 else 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  fin_cases t <;> fin_cases t' <;> simp [f] <;> norm_num

lemma f_conj (a : ZMod 2) (t : Fin 2) : conj (f a t) = f a t := by simp [f]

def s0 (n : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℂ)

lemma s0_sq (n : ℕ) : s0 n * s0 n = ((2 : ℂ)^n)⁻¹ := by
  simp only [s0]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast; rfl

lemma s0_conj (n : ℕ) : conj (s0 n) = s0 n := by simp [s0]

lemma xKet_eq {n : ℕ} (c : BinaryWord n) (z : Fin n → Fin 2) :
    xKet c z = s0 n * ∏ i, f (c i) (z i) := by
  simp [xKet, f, s0, Finset.prod_pow_eq_pow_sum]


lemma sum_prod {n : ℕ} {α : Type} [Fintype α] [DecidableEq α] (g : Fin n → α → ℂ) :
    ∑ z : Fin n → α, ∏ i, g i (z i) = ∏ i, ∑ a, g i a := (Fintype.prod_sum g).symm

lemma prod_ite2 {n : ℕ} {α : Type} [DecidableEq α] (c d : Fin n → α) :
    (∏ i : Fin n, if c i = d i then (2:ℂ) else 0) = if c = d then 2^n else 0 := by
  rw [Fintype.prod_ite_zero]; simp [funext_iff]

lemma xKet_star {n : ℕ} (c : BinaryWord n) (z : Fin n → Fin 2) : star (xKet c z) = xKet c z := by
  rw [xKet_eq]; simp [s0_conj, f_conj]

lemma xKet_conj {n : ℕ} (c : BinaryWord n) (z : Fin n → Fin 2) :
    (starRingEnd ℂ) (xKet c z) = xKet c z := xKet_star c z

lemma charsum_cd {n : ℕ} (c d : BinaryWord n) :
    ∑ z, xKet c z * xKet d z = if c = d then 1 else 0 := by
  simp only [xKet_eq]
  have : ∀ z : Fin n → Fin 2, s0 n * (∏ i, f (c i) (z i)) * (s0 n * ∏ i, f (d i) (z i))
      = s0 n * s0 n * ∏ i, (fun i t => f (c i) t * f (d i) t) i (z i) := by
    intro z; simp only [Finset.prod_mul_distrib]; ring
  have h2 : ∑ z : Fin n → Fin 2, ∏ i, (f (c i) (z i) * f (d i) (z i)) =
      ∏ i, ∑ t, f (c i) t * f (d i) t := sum_prod (fun i t => f (c i) t * f (d i) t)
  simp only [this, ← Finset.mul_sum]
  rw [h2]
  simp only [f_sum_left, prod_ite2, s0_sq]
  split_ifs <;> simp

lemma charsum_zz {n : ℕ} (z z' : Fin n → Fin 2) :
    ∑ c : BinaryWord n, xKet c z * xKet c z' = if z = z' then 1 else 0 := by
  simp only [xKet_eq]
  have : ∀ c : BinaryWord n, s0 n * (∏ i, f (c i) (z i)) * (s0 n * ∏ i, f (c i) (z' i))
      = s0 n * s0 n * ∏ i, (fun i a => f a (z i) * f a (z' i)) i (c i) := by
    intro c; simp only [Finset.prod_mul_distrib]; ring
  have h2 : ∑ c : BinaryWord n, ∏ i, (f (c i) (z i) * f (c i) (z' i)) =
      ∏ i, ∑ a, f a (z i) * f a (z' i) := sum_prod (fun i a => f a (z i) * f a (z' i))
  simp only [this, ← Finset.mul_sum]
  rw [h2]
  simp only [f_sum_right, prod_ite2, s0_sq]
  split_ifs <;> simp

def Fm (n : ℕ) : Matrix (Fin n → Fin 2) (BinaryWord n) ℂ := Matrix.of fun z c => xKet c z

lemma FhF (n : ℕ) : ((Fm n)ᴴ * Fm n : Matrix (BinaryWord n) (BinaryWord n) ℂ) = 1 := by
  ext c d
  simp [Matrix.mul_apply, Fm, xKet_star, charsum_cd, Matrix.one_apply]

lemma FFh (n : ℕ) : (Fm n * (Fm n)ᴴ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = 1 := by
  ext z z'
  simp [Matrix.mul_apply, Fm, xKet_star, charsum_zz, Matrix.one_apply]

def Tm {n : ℕ} (u : BinaryWord n) : Matrix (BinaryWord n) (BinaryWord n) ℂ :=
  Matrix.of fun c' c => if c' = c + u then 1 else 0

lemma ZF {n : ℕ} (u : BinaryWord n) : zError u * Fm n = Fm n * Tm u := by
  ext z c
  rw [zError, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Fm, Tm, Matrix.of_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [xKet_eq, xKet_eq, ← Finset.prod_pow_eq_pow_sum]
  simp only [Pi.add_apply, f_add, Finset.prod_mul_distrib]
  simp only [f]; ring

def Dm {n r : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord r) (s : BinaryWord r) :
    Matrix (BinaryWord n) (BinaryWord n) ℂ :=
  Matrix.diagonal fun c => if H c = s then 1 else 0

lemma P_eq {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k)) (s : BinaryWord (n-k)) :
    syndromeProjector H s = Fm n * Dm H s * (Fm n)ᴴ := by
  ext z z'
  rw [Dm, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [syndromeProjector, Matrix.sum_apply,
    Fm, Matrix.of_apply, Matrix.conjTranspose_apply, xKet_star]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp [pureDensity, xKet_conj]


def Em (k : ℕ) : Fin (2^k) ≃ BinaryWord k :=
  (finCongr (by simp [BinaryWord])).trans (Fintype.equivFin (BinaryWord k)).symm

def Jm {n k : ℕ} (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) :
    Matrix (BinaryWord n) (Fin (2^k)) ℂ :=
  Matrix.of fun c m => if c = word (Em k m) then 1 else 0

lemma V_eq {n k : ℕ} (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) :
    cssIsometry word = Fm n * Jm word := by
  ext z m
  simp only [Matrix.mul_apply, Fm, Jm, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

lemma JhJ {n k : ℕ} (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word) :
    ((Jm word)ᴴ * Jm word : Matrix (Fin (2^k)) (Fin (2^k)) ℂ) = 1 := by
  ext m m'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Jm, Matrix.of_apply, Matrix.one_apply]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [hword.eq_iff, (Em k).injective.eq_iff, eq_comm]

def Bm {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) : Matrix (Fin (2^k)) (BinaryWord n) ℂ :=
  (Jm word)ᴴ * Tm (estimate s) * Dm H s

lemma B_apply {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) (m : Fin (2^k)) (c : BinaryWord n) :
    Bm H word estimate s m c = if word (Em k m) = c + estimate s ∧ H c = s then 1 else 0 := by
  rw [Bm, Dm, Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Jm, Tm, Matrix.of_apply]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp_all

lemma K_eq {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) :
    (cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s
      = Bm H word estimate s * (Fm n)ᴴ := by
  rw [V_eq, P_eq, Matrix.conjTranspose_mul, Bm]
  have : (Jm word)ᴴ * (Fm n)ᴴ * zError (estimate s) * (Fm n * Dm H s * (Fm n)ᴴ)
      = (Jm word)ᴴ * ((Fm n)ᴴ * (zError (estimate s) * Fm n)) * Dm H s * (Fm n)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [this, ZF, ← Matrix.mul_assoc (Fm n)ᴴ, FhF, Matrix.one_mul]

lemma Hw_zero {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n)
    (hker : LinearMap.range word = LinearMap.ker H) (x : BinaryWord k) : H (word x) = 0 := by
  have : word x ∈ LinearMap.ker H := hker ▸ LinearMap.mem_range_self word x
  simpa using this

lemma sum_cw {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word)
    (hker : LinearMap.range word = LinearMap.ker H) (d : BinaryWord n) (hd : H d = 0) :
    ∑ m : Fin (2^k), (if word (Em k m) = d then (1:ℂ) else 0) = 1 := by
  have : d ∈ LinearMap.range word := hker ▸ (by simpa using hd)
  obtain ⟨w0, rfl⟩ := this
  rw [Equiv.sum_comp (Em k) (fun w => if word w = word w0 then (1:ℂ) else 0)]
  simp [hword.eq_iff]

lemma add_eq_zero_iff2 {n : ℕ} (u e : BinaryWord n) : u + e = 0 ↔ u = e := by
  rw [add_eq_zero_iff_eq_neg]
  have : -e = e := funext fun i => ZMod.neg_eq_self_mod_two (e i)
  rw [this]

lemma BhB {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n) (hestimate : ∀ s, H (estimate s) = s) :
    (∑ s, (Bm H word estimate s)ᴴ * Bm H word estimate s :
      Matrix (BinaryWord n) (BinaryWord n) ℂ) = 1 := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, B_apply]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (H c)]
  · by_cases hcd : c = d
    · subst hcd
      simp only [and_true, Matrix.one_apply_eq]
      have h0 : H (c + estimate (H c)) = 0 := by
        rw [map_add, hestimate]
        exact (add_eq_zero_iff2 _ _).mpr rfl
      refine Eq.trans ?_ (sum_cw H word hword hker _ h0)
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> rfl
    · rw [Matrix.one_apply_ne hcd]
      apply Finset.sum_eq_zero
      intro m _
      split_ifs with h1 h2
      · exact absurd (add_right_cancel (h1.1.symm.trans h2.1)) hcd
      · rfl
      · rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro m _
    split_ifs with h1 h2
    · exact absurd h1.2.symm hb
    · rfl
    · rfl
  · simp


lemma isChannel_kraus {ι κ K : Type} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K, fun j => E ((Fintype.equivFin K).symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [Equiv.sum_comp (Fintype.equivFin K).symm (fun j => (E j)ᴴ * E j)]
    exact hE
  · intro ρ
    unfold krausApply
    rw [Equiv.sum_comp (Fintype.equivFin K).symm (fun j => E j * ρ * (E j)ᴴ)]

lemma enc_channel {n k : ℕ} (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n)
    (hword : Function.Injective word) : IsChannel (conjSuperop (cssIsometry word)) := by
  have h := isChannel_kraus (fun _ : Unit => cssIsometry word) (by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [V_eq, Matrix.conjTranspose_mul]
    have : (Jm word)ᴴ * (Fm n)ᴴ * (Fm n * Jm word) = (Jm word)ᴴ * ((Fm n)ᴴ * Fm n) * Jm word := by
      simp only [Matrix.mul_assoc]
    rw [this, FhF, Matrix.mul_one, JhJ word hword])
  obtain ⟨m, E, hE, hρ⟩ := h
  exact ⟨m, E, hE, fun ρ => by rw [← hρ]; simp [krausApply, conjSuperop]⟩

lemma dec_channel {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n) (hestimate : ∀ s, H (estimate s) = s) :
    IsChannel (cssDecoder H word estimate) := by
  unfold cssDecoder
  apply isChannel_kraus
  simp only [K_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have : ∀ s, Fm n * (Bm H word estimate s)ᴴ * (Bm H word estimate s * (Fm n)ᴴ)
      = Fm n * ((Bm H word estimate s)ᴴ * Bm H word estimate s) * (Fm n)ᴴ := by
    intro s; simp only [Matrix.mul_assoc]
  simp only [this]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, BhB H word hword hker estimate hestimate, Matrix.mul_one, FFh]

lemma KZV {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) (u : BinaryWord n) :
    (cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s * zError u * cssIsometry word
      = Bm H word estimate s * Tm u * Jm word := by
  rw [K_eq]
  have : Bm H word estimate s * (Fm n)ᴴ * zError u * cssIsometry word
      = Bm H word estimate s * ((Fm n)ᴴ * (zError u * Fm n)) * Jm word := by
    rw [V_eq]; simp only [Matrix.mul_assoc]
  rw [this, ZF, ← Matrix.mul_assoc (Fm n)ᴴ, FhF, Matrix.one_mul]

lemma trace_A {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) (u : BinaryWord n) :
    (Bm H word estimate s * Tm u * Jm word).trace
      = if u = estimate s ∧ H u = s then (2:ℂ)^k else 0 := by
  have hdiag : ∀ m, (Bm H word estimate s * Tm u * Jm word) m m
      = if u = estimate s ∧ H u = s then 1 else 0 := by
    intro m
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hTJ : ∀ c, (Tm u * Jm word) c m = if c = word (Em k m) + u then 1 else 0 := by
      intro c
      simp only [Matrix.mul_apply, Tm, Jm, Matrix.of_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hTJ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      B_apply, map_add, Hw_zero H word hker, zero_add]
    congr 1
    apply propext
    rw [show word (Em k m) + u + estimate s = word (Em k m) + (u + estimate s) by abel]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(add_eq_zero_iff2 _ _).mp ?_, h2⟩
      have := congrArg (fun x => x - word (Em k m)) h1
      simpa using this.symm
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [(add_eq_zero_iff2 _ _).mpr h1, add_zero]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  split_ifs <;> simp


lemma qD_single (g : ℝ) (a b c d : Fin 2) :
    QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing g (Matrix.single a b 1) c d
      = if a = c ∧ b = d then (if c = d then 1 else (g:ℂ)) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing]

lemma qsum (γ : ℝ) (t t' : Fin 2) :
    ∑ a : ZMod 2, ((if a = 0 then 1 - γ else γ : ℝ) : ℂ) * (f a t * f a t')
      = if t = t' then 1 else ((1 - 2*γ : ℝ) : ℂ) := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  fin_cases t <;> fin_cases t' <;> simp [f] <;> ring

lemma zError_ct {n : ℕ} (u : BinaryWord n) : (zError u)ᴴ = zError u := by
  rw [zError, Matrix.diagonal_conjTranspose]
  congr 1
  funext z
  simp

lemma zError_diag {n : ℕ} (u : BinaryWord n) (z : Fin n → Fin 2) :
    (-1 : ℂ) ^ (∑ i, (u i).val * (z i).val) = ∏ i, f (u i) (z i) := by
  rw [← Finset.prod_pow_eq_pow_sum]; rfl

lemma ZYZ {n : ℕ} (u : BinaryWord n) (Y : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (y y' : Fin n → Fin 2) :
    (zError u * Y * (zError u)ᴴ) y y' = (∏ i, f (u i) (y i)) * Y y y' * ∏ i, f (u i) (y' i) := by
  rw [zError_ct, zError, Matrix.mul_diagonal, Matrix.diagonal_mul, zError_diag, zError_diag]

lemma N_eq {n : ℕ} (γ : ℝ) (Y : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    piSuperop (fun _ : Fin n =>
        QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*γ)) Y
      = ∑ u : BinaryWord n, ((phaseErrorProbability γ u : ℝ) : ℂ) • (zError u * Y * (zError u)ᴴ) := by
  ext y y'
  have hL : piSuperop (fun _ : Fin n =>
        QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*γ)) Y y y'
      = Y y y' * ∏ i, (if y i = y' i then 1 else ((1-2*γ : ℝ) : ℂ)) := by
    simp only [piSuperop, Matrix.of_apply, qD_single]
    rw [Finset.sum_eq_single y, Finset.sum_eq_single y']
    · rw [Fintype.prod_ite_zero, if_pos (fun i => ⟨rfl, rfl⟩)]
    · intro b _ hb
      rw [Fintype.prod_ite_zero, if_neg, mul_zero]
      intro h; exact hb (funext fun i => ((h i).2))
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro x' _
      rw [Fintype.prod_ite_zero, if_neg, mul_zero]
      intro h; exact hb (funext fun i => ((h i).1))
    · simp
  rw [hL, Matrix.sum_apply]
  simp only [Matrix.smul_apply, ZYZ, smul_eq_mul, phaseErrorProbability, Complex.ofReal_prod]
  have : ∀ u : BinaryWord n, (∏ i, ((if u i = 0 then 1 - γ else γ : ℝ) : ℂ)) *
      ((∏ i, f (u i) (y i)) * Y y y' * ∏ i, f (u i) (y' i))
      = Y y y' * ∏ i, (fun i a => ((if a = 0 then 1 - γ else γ : ℝ) : ℂ) * (f a (y i) * f a (y' i))) i (u i) := by
    intro u; simp only [Finset.prod_mul_distrib]; ring
  simp only [this]
  rw [← Finset.mul_sum, sum_prod (α := ZMod 2)
    (fun i a => ((if a = 0 then 1 - γ else γ : ℝ) : ℂ) * (f a (y i) * f a (y' i)))]
  simp only [qsum]


lemma conj_single_entry {M : ℕ} (B : Matrix (Fin M) (Fin M) ℂ) (b a : Fin M) (c : ℂ) :
    (B * (c • Matrix.single b a 1) * Bᴴ : Matrix (Fin M) (Fin M) ℂ) b a
      = c * (B b b * star (B a a)) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, ite_and]
  ring

lemma collapse {M : ℕ} (g : Fin M → Fin M → Fin M → Fin M → ℂ) :
    (∑ x, ∑ x1, ∑ x2, ∑ x3, if x = x1 then (if x2 = x3 then g x x1 x2 x3 else 0) else 0)
      = ∑ x, ∑ x2, g x x x2 x2 := by
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma G {M : ℕ} [NeZero M] {ι κ : Type} [Fintype ι] [Fintype κ] (Φ : Superop (Fin M) (Fin M))
    (w : κ → ℂ) (A : ι → κ → Matrix (Fin M) (Fin M) ℂ)
    (hΦ : ∀ X, Φ X = ∑ i, ∑ j, w j • (A i j * X * (A i j)ᴴ)) :
    effectProb (pureDensity (finiteMaxEntangled (Fin M)))
      (idTensorSuperop Φ (pureDensity (finiteMaxEntangled (Fin M))))
      = (∑ i, ∑ j, w j * ((A i j).trace * conj (A i j).trace) / ((M:ℂ)^2)).re := by
  unfold effectProb
  congr 1
  set r : ℂ := ((Real.sqrt (Fintype.card (Fin M)))⁻¹ : ℂ) with hr
  have hrr : r * conj r = ((M:ℂ))⁻¹ := by
    rw [hr, Fintype.card_fin]
    have hc : (starRingEnd ℂ) ((Real.sqrt M : ℂ))⁻¹ = ((Real.sqrt M : ℂ))⁻¹ := by simp
    rw [hc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hX : ∀ b a : Fin M, (Matrix.of fun i i' =>
      pureDensity (finiteMaxEntangled (Fin M)) (b, i) (a, i')) = (r * conj r) • Matrix.single b a 1 := by
    intro b a
    ext i i'
    have hc : (starRingEnd ℂ) ((Real.sqrt M : ℂ))⁻¹ = ((Real.sqrt M : ℂ))⁻¹ := by simp
    by_cases h1 : b = i <;> by_cases h2 : a = i' <;>
      simp [pureDensity, finiteMaxEntangled, Matrix.single_apply, hr, h1, h2, hc]
  have hP : ∀ x x1 x2 x3 : Fin M, pureDensity (finiteMaxEntangled (Fin M)) (x, x1) (x2, x3)
      = if x = x1 then (if x2 = x3 then r * conj r else 0) else 0 := by
    intro x x1 x2 x3
    by_cases h1 : x = x1 <;> by_cases h2 : x2 = x3 <;>
      simp [pureDensity, finiteMaxEntangled, hr, h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, idTensorSuperop,
    Matrix.of_apply, hX]
  simp only [hΦ, Matrix.sum_apply, Matrix.smul_apply, conj_single_entry, hP, ite_mul, zero_mul,
    hrr]
  refine (collapse _).trans ?_
  simp only [conj_single_entry]
  have hR : ∀ i j, w j * ((∑ b, A i j b b) * (starRingEnd ℂ) (∑ a, A i j a a)) / (M:ℂ) ^ 2
      = ∑ x, ∑ x1, (M:ℂ)⁻¹ * (w j • ((M:ℂ)⁻¹ * (A i j x1 x1 * star (A i j x x)))) := by
    intro i j
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro x1 _
    simp only [smul_eq_mul, Complex.star_def]
    field_simp
  simp only [hR, Finset.mul_sum]
  calc _ = ∑ x, ∑ i, ∑ x1, ∑ j, (M:ℂ)⁻¹ * (w j • ((M:ℂ)⁻¹ * (A i j x1 x1 * star (A i j x x)))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ j, ∑ x1, (M:ℂ)⁻¹ * (w j • ((M:ℂ)⁻¹ * (A i j x1 x1 * star (A i j x x)))) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ j, ∑ x1, (M:ℂ)⁻¹ * (w j • ((M:ℂ)⁻¹ * (A i j x1 x1 * star (A i j x x)))) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm


def Am {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) (u : BinaryWord n) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
  Bm H word estimate s * Tm u * Jm word

lemma key {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (estimate : BinaryWord (n-k) → BinaryWord n)
    (s : BinaryWord (n-k)) (u : BinaryWord n) (X : Matrix (Fin (2^k)) (Fin (2^k)) ℂ) :
    (cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s *
        (zError u * (cssIsometry word * X * (cssIsometry word)ᴴ) * (zError u)ᴴ) *
        ((cssIsometry word)ᴴ * zError (estimate s) * syndromeProjector H s)ᴴ
      = Am H word estimate s u * X * (Am H word estimate s u)ᴴ := by
  rw [Am, ← KZV]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma cls_eq {n k : ℕ} (gamma : ℝ) (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n) :
    classicalLinearSuccess gamma H word estimate
      = ∑ u : BinaryWord n, if estimate (H u) = u then phaseErrorProbability gamma u else 0 := by
  unfold classicalLinearSuccess
  have h : ∀ m : BinaryWord k, (∑ u : BinaryWord n,
      if word m + u - estimate (H (word m + u)) = word m then phaseErrorProbability gamma u else 0)
      = ∑ u : BinaryWord n, if estimate (H u) = u then phaseErrorProbability gamma u else 0 := by
    intro m
    apply Finset.sum_congr rfl; intro u _
    congr 1
    apply propext
    rw [map_add, Hw_zero H word hker, zero_add, add_sub_assoc, add_eq_left, sub_eq_zero, eq_comm]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (BinaryWord k) : ℝ) = 2^k := by
    simp [BinaryWord, Fintype.card_fun, ZMod.card]
  rw [this, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

lemma lhs_eq {n k : ℕ} (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k))
    (estimate : BinaryWord (n-k) → BinaryWord n) (p : BinaryWord n → ℝ) :
    (∑ s : BinaryWord (n-k), ∑ u : BinaryWord n, if u = estimate s ∧ H u = s then p u else 0)
      = ∑ u : BinaryWord n, if estimate (H u) = u then p u else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.sum_eq_single (H u)]
  · simp [eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

end A3S54P04

open QAlgorithms.Papers.Independent.Support50.P04 in
theorem solution {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k)) (hH : Function.Surjective H)
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n) (hestimate : ∀ s, H (estimate s) = s)
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ C : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode (Fin n → Fin 2) (Fin n → Fin 2),
      C.M = 2^k ∧
      HEq C.encoder (conjSuperop (cssIsometry word)) ∧
      HEq C.decoder (cssDecoder H word estimate) ∧
      QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity (piSuperop (fun _ : Fin n => (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)))) C = classicalLinearSuccess gamma H word estimate := by
  refine ⟨⟨2^k, by positivity, conjSuperop (cssIsometry word), cssDecoder H word estimate,
    A3S54P04.enc_channel word hword,
    A3S54P04.dec_channel H word hword hker estimate hestimate⟩, rfl, HEq.rfl, HEq.rfl, ?_⟩
  have hΦ : ∀ X, cssDecoder H word estimate
      (piSuperop (fun _ : Fin n =>
        QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma))
        (conjSuperop (cssIsometry word) X))
      = ∑ s, ∑ u, ((phaseErrorProbability gamma u : ℝ) : ℂ) •
        (A3S54P04.Am H word estimate s u * X * (A3S54P04.Am H word estimate s u)ᴴ) := by
    intro X
    simp only [cssDecoder, krausApply, conjSuperop, A3S54P04.N_eq, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro u _
    rw [A3S54P04.key]
  have hG := A3S54P04.G (M := 2^k) _ _ _ hΦ
  refine hG.trans ?_
  simp only [A3S54P04.Am, A3S54P04.trace_A H word hker estimate]
  have hterm : ∀ s u, ((phaseErrorProbability gamma u : ℝ) : ℂ) *
      ((if u = estimate s ∧ H u = s then (2:ℂ)^k else 0) *
        (starRingEnd ℂ) (if u = estimate s ∧ H u = s then (2:ℂ)^k else 0)) / ((2^k : ℕ) : ℂ)^2
      = ((if u = estimate s ∧ H u = s then phaseErrorProbability gamma u else 0 : ℝ) : ℂ) := by
    intro s u
    split_ifs
    · push_cast
      simp only [map_pow, Complex.conj_ofNat]
      field_simp
    · simp
  simp only [hterm, Complex.re_sum, Complex.ofReal_re]
  rw [A3S54P04.lhs_eq, A3S54P04.cls_eq gamma H word hker estimate]

end
