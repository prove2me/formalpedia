-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.zero_entanglement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:49:32.066987+00:00
-- url     : https://prove2.me/submissions/7279c5b4-1902-4506-8d31-c5fa7c460571

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- a unit vector `v` with `v v† = Σ φ_k φ_k†` forces every `φ_k ∈ span v`. -/
lemma rank1_split {α ι : Type*} [Fintype α] [Fintype ι] (v : α → ℂ) (hv : ∑ a, v a * conj (v a) = 1)
    (φ : ι → α → ℂ) (h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b)) (k : ι) :
    ∀ a, φ k a = (∑ b, conj (v b) * φ k b) * v a := by
  set c := ∑ b, conj (v b) * φ k b
  set ψ : α → ℂ := fun a => φ k a - c * v a
  have nsq : ∀ u w : α → ℂ, ((Complex.normSq (∑ a, conj (u a) * w a) : ℝ) : ℂ) =
      ∑ a, ∑ b, conj (u a) * (w a * conj (w b)) * u b := by
    intro u w
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  have hQ : ∀ ψ : α → ℂ, Complex.normSq (∑ a, conj (ψ a) * v a) =
      ∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) := by
    intro ψ
    have : ((Complex.normSq (∑ a, conj (ψ a) * v a) : ℝ) : ℂ) =
        ((∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) : ℝ) : ℂ) := by
      rw [nsq]; push_cast; simp_rw [nsq, h, Finset.mul_sum, Finset.sum_mul]
      calc ∑ a, ∑ b, ∑ j, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b
          = ∑ a, ∑ j, ∑ b, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    exact_mod_cast this
  have hψv : ∑ a, conj (ψ a) * v a = 0 := by
    have : ∑ a, conj (v a) * ψ a = 0 := by
      simp only [ψ, mul_sub, Finset.sum_sub_distrib]
      have : ∑ a, conj (v a) * (c * v a) = c * ∑ a, v a * conj (v a) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hv, mul_one]; simp [c]
    have := congrArg conj this
    rw [map_sum, map_zero] at this
    rw [← this]; exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]
  have hψφ : ∑ a, conj (ψ a) * φ k a = ∑ a, conj (ψ a) * ψ a := by
    have : ∀ a, φ k a = ψ a + c * v a := fun a => by simp [ψ]
    simp_rw [this, mul_add, Finset.sum_add_distrib]
    have : ∑ a, conj (ψ a) * (c * v a) = c * ∑ a, conj (ψ a) * v a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hψv, mul_zero, add_zero]
  have hz := hQ ψ
  rw [hψv, map_zero] at hz
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hz.symm k
    (Finset.mem_univ k)
  rw [hψφ, Complex.normSq_eq_zero] at hk
  have hn : ∑ a, Complex.normSq (ψ a) = 0 := by
    have : ((∑ a, Complex.normSq (ψ a) : ℝ) : ℂ) = 0 := by
      push_cast; rw [← hk]
      exact Finset.sum_congr rfl fun a _ => by rw [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast this
  intro a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 hn a
    (Finset.mem_univ a)
  rw [Complex.normSq_eq_zero] at this
  simp only [ψ, sub_eq_zero] at this
  exact this

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

lemma cfc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = (∑ i, negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp only [Complex.re_sum, Complex.ofReal_re, negMulLog, Real.logb, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- zero entropy density matrix is a pure projector. -/
lemma pure_of_vn {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (h0 : vnEntropy ρ = 0) :
    ∃ w : EuclideanSpace ℂ I, ‖w‖ = 1 ∧ ρ = pureDensity w := by
  set h := hρ.1
  set lam := h.eigenvalues
  set v := h.eigenvectorBasis
  have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hsum : ∑ k, lam k = 1 := by
    have := h.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  have hle1 : ∀ k, lam k ≤ 1 := fun k => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ k)
  have hS : ∑ k, negMulLog (lam k) = 0 := by
    rw [vn_eig h] at h0
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · exact h0
    · exfalso; exact (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne' h0
  have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.negMulLog_nonneg (hl0 j) (hle1 j))).1
      hS k (Finset.mem_univ k)
    rcases (hl0 k).eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases (hle1 k).eq_or_lt with h' | h'
    · exact Or.inr h'
    exfalso
    have : lam k * Real.log (lam k) < 0 := mul_neg_of_pos_of_neg h (Real.log_neg h h')
    rw [Real.negMulLog] at *; linarith
  obtain ⟨i0, hi0⟩ : ∃ i0, lam i0 = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ k, lam k = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hc k)
    linarith
  have hother : ∀ k, k ≠ i0 → lam k = 0 := by
    have hs := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i0)
    rw [hsum, hi0] at hs
    have h0 : ∑ k ∈ Finset.univ.erase i0, lam k = 0 := by linarith
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hl0 k)).1 h0 k
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
  refine ⟨v i0, hv i0, ?_⟩
  rw [spec_sum h]
  rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [lam, hother k hk]) (by simp)]
  simp [lam, hi0]
  rfl

lemma unit_sum {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    ∑ i, v i * conj (v i) = 1 := by
  have h1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
  have : ∑ i, v i * conj (v i) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [this, h1]; simp

end X4ZE

-- ===== ZEB =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P32 (pairOfState)
open scoped Matrix ComplexConjugate ComplexOrder

/-- separable (sum of product pure terms), stated through zero-extended entries. -/
def Sep (s : Shared) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ), ∀ x y : Fin 2 → ℕ,
    (∀ i, x i < s.dims i) → (∀ i, y i < s.dims i) →
      stateEntry s x y = ∑ k, f k (x 0) * g k (x 1) * conj (f k (y 0) * g k (y 1))

lemma se_in (s : Shared) (x y : Fin 2 → ℕ) (hx : ∀ i, x i < s.dims i) (hy : ∀ i, y i < s.dims i) :
    stateEntry s x y = s.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩) := by
  unfold stateEntry; rw [dif_pos ⟨hx, hy⟩]

lemma rho_se (s : Shared) (a b : RegisterBasis (fun i => Fin (s.dims i))) :
    s.rho a b = stateEntry s (fun i => (a i).val) (fun i => (b i).val) := by
  rw [se_in s _ _ (fun i => (a i).isLt) (fun i => (b i).isLt)]

lemma rho_of_sep {s : Shared} (hS : Sep s) : ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ),
    ∀ a b : RegisterBasis (fun i => Fin (s.dims i)), s.rho a b =
      ∑ k, (f k (a 0).val * g k (a 1).val) * conj (f k (b 0).val * g k (b 1).val) := by
  obtain ⟨ι, _, f, g, h⟩ := hS
  exact ⟨ι, inferInstance, f, g, fun a b => by
    rw [rho_se, h _ _ (fun i => (a i).isLt) (fun i => (b i).isLt)]⟩

lemma sandwich {m n ι : Type*} [Fintype n] [Fintype ι] (L : Matrix m n ℂ) (ρ : Matrix n n ℂ)
    (h : ι → n → ℂ) (hρ : ∀ a b, ρ a b = ∑ k, h k a * conj (h k b)) (X Y : m) :
    (L * ρ * Lᴴ) X Y = ∑ k, (∑ a, L X a * h k a) * conj (∑ b, L Y b * h k b) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, hρ, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sep_of (t : Shared) (ι : Type) [Fintype ι] (K : ι → RegisterBasis (fun i => Fin (t.dims i)) → ℂ)
    (c : ℝ) (hc : 0 < c) (hK : ∀ X Y, (c : ℂ) * t.rho X Y = ∑ i, K i X * conj (K i Y))
    (F G : ι → ℕ → ℂ) (hFG : ∀ i X, K i X = F i (X 0).val * G i (X 1).val) : Sep t := by
  refine ⟨ι, inferInstance, fun i n => ((Real.sqrt c)⁻¹ : ℝ) * F i n, G, fun x y hx hy => ?_⟩
  rw [se_in t x y hx hy]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e := hK (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
  have hs : ((Real.sqrt c)⁻¹ : ℝ) * ((Real.sqrt c)⁻¹ : ℝ) = (c⁻¹ : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le]
  have hsC : ((Real.sqrt c)⁻¹ : ℂ) * ((Real.sqrt c)⁻¹ : ℂ) = (c : ℂ)⁻¹ := by
    exact_mod_cast hs
  calc t.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)
      = (c : ℂ)⁻¹ * ((c : ℂ) * t.rho (fun i => ⟨x i, hx i⟩) (fun i => ⟨y i, hy i⟩)) := by
        field_simp
    _ = _ := by
      rw [e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hFG, hFG]
      push_cast
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      rw [← hsC]; ring

lemma sum_pi2 {d : Fin 2 → ℕ} (F : ((i : Fin 2) → Fin (d i)) → ℂ) :
    ∑ a, F a = ∑ q : Fin (d 0) × Fin (d 1), F ((piFinTwoEquiv (fun i => Fin (d i))).symm q) :=
  (Equiv.sum_comp (piFinTwoEquiv (fun i => Fin (d i))).symm F).symm

lemma K0 (s t : Shared) (A : Matrix (Fin (t.dims 0)) (Fin (s.dims 0)) ℂ) (hd1 : t.dims 1 = s.dims 1)
    (f g : ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 0 A X a * (f (a 0).val * g (a 1).val) =
      (∑ τ, A (X 0) τ * f τ.val) * g (X 1).val := by
  rw [sum_pi2, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlt : (X 1).val < s.dims 1 := hd1 ▸ (X 1).isLt
  rw [Finset.sum_eq_single ⟨(X 1).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two]; ring
  · intro u _ hu
    have : ¬ ((X 1).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma K1 (s t : Shared) (A : Matrix (Fin (t.dims 1)) (Fin (s.dims 1)) ℂ) (hd0 : t.dims 0 = s.dims 0)
    (f g : ℕ → ℂ) (X : RegisterBasis (fun i => Fin (t.dims i))) :
    ∑ a, liftLocalKraus s t 1 A X a * (f (a 0).val * g (a 1).val) =
      f (X 0).val * ∑ τ, A (X 1) τ * g τ.val := by
  rw [sum_pi2, Fintype.sum_prod_type]
  have hlt : (X 0).val < s.dims 0 := hd0 ▸ (X 0).isLt
  rw [Finset.sum_eq_single ⟨(X 0).val, hlt⟩]
  · simp [liftLocalKraus, Fin.forall_fin_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · intro u _ hu
    have : ¬ ((X 0).val = u.val) := fun h => hu (Fin.ext h.symm)
    simp [liftLocalKraus, Fin.forall_fin_two, this]
  · simp

lemma sep_step {s : Shared} {k : ℕ} {p : Fin k → ℝ} {r : Fin k → Shared} (h : LocalInstrument s p r)
    (hS : Sep s) (j : Fin k) (hp : 0 < p j) : Sep (r j) := by
  obtain ⟨_, _, party, count, A, hd, _, hsub⟩ := h
  obtain ⟨ι, _, f, g, hρ⟩ := rho_of_sep hS
  have hK : ∀ X Y, ((p j : ℝ) : ℂ) * (r j).rho X Y = ∑ i : Fin (count j) × ι,
      (∑ a, liftLocalKraus s (r j) party (A j i.1) X a * (f i.2 (a 0).val * g i.2 (a 1).val)) *
      conj (∑ b, liftLocalKraus s (r j) party (A j i.1) Y b * (f i.2 (b 0).val * g i.2 (b 1).val)) := by
    intro X Y
    have e := congrFun (congrFun (hsub j) X) Y
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply] at e
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact sandwich (liftLocalKraus s (r j) party (A j z)) s.rho
      (fun i a => f i (a 0).val * g i (a 1).val) hρ X Y
  obtain rfl | rfl : party = 0 ∨ party = 1 := by fin_cases party <;> simp
  · refine sep_of (r j) _ _ (p j) hp hK
      (fun i n => if h : n < (r j).dims 0 then ∑ τ, A j i.1 ⟨n, h⟩ τ * f i.2 τ.val else 0)
      (fun i n => g i.2 n) fun i X => ?_
    rw [K0 s (r j) _ (hd j 1 (by decide)), dif_pos (X 0).isLt]
  · refine sep_of (r j) _ _ (p j) hp hK (fun i n => f i.2 n)
      (fun i n => if h : n < (r j).dims 1 then ∑ τ, A j i.1 ⟨n, h⟩ τ * g i.2 τ.val else 0)
      fun i X => ?_
    rw [K1 s (r j) _ (hd j 0 (by decide)), dif_pos (X 1).isLt]

lemma sep_list (d : Fin 2 → ℕ) (l : List (ℝ × Shared)) (hd : ∀ w ∈ l, w.2.dims = d)
    (h0 : ∀ w ∈ l, 0 ≤ w.1) (hS : ∀ w ∈ l, 0 < w.1 → Sep w.2) :
    ∃ (ι : Type) (_ : Fintype ι) (f g : ι → ℕ → ℂ), ∀ x y : Fin 2 → ℕ,
      (∀ i, x i < d i) → (∀ i, y i < d i) →
        (l.map fun w => (w.1 : ℂ) * stateEntry w.2 x y).sum =
          ∑ k, f k (x 0) * g k (x 1) * conj (f k (y 0) * g k (y 1)) := by
  induction l with
  | nil => exact ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun x y _ _ => by simp⟩
  | cons w l ih =>
    obtain ⟨ι, _, f, g, hl⟩ := ih (fun v hv => hd v (List.mem_cons_of_mem _ hv))
      (fun v hv => h0 v (List.mem_cons_of_mem _ hv)) (fun v hv => hS v (List.mem_cons_of_mem _ hv))
    rcases (h0 w List.mem_cons_self).eq_or_lt with hw | hw
    · refine ⟨ι, inferInstance, f, g, fun x y hx hy => ?_⟩
      rw [List.map_cons, List.sum_cons, ← hw, hl x y hx hy]; simp
    obtain ⟨κ, _, f1, g1, h1⟩ := hS w List.mem_cons_self hw
    have hdw := hd w List.mem_cons_self
    refine ⟨κ ⊕ ι, inferInstance, Sum.elim (fun k n => ((Real.sqrt w.1 : ℝ) : ℂ) * f1 k n) f,
      Sum.elim g1 g, fun x y hx hy => ?_⟩
    rw [List.map_cons, List.sum_cons, hl x y hx hy, Fintype.sum_sum_type,
      h1 x y (fun i => hdw ▸ hx i) (fun i => hdw ▸ hy i), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : ((Real.sqrt w.1 : ℝ) : ℂ) * ((Real.sqrt w.1 : ℝ) : ℂ) = (w.1 : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hw.le
    simp only [Sum.elim_inl, map_mul, Complex.conj_ofReal]
    rw [← hs]; ring

lemma main {s : Shared} {out : List (ℝ × Shared)} (h : LocalTree s out) :
    (∀ w ∈ out, 0 ≤ w.1) ∧ (Sep s → ∀ w ∈ out, 0 < w.1 → Sep w.2) := by
  induction h with
  | stop s => exact ⟨fun w hw => by simp at hw; simp [hw], fun hS w hw _ => by simp at hw; simp [hw, hS]⟩
  | step s k p r hI next hn ih =>
    have hp0 := hI.1
    refine ⟨fun w hw => ?_, fun hS w hw hpos => ?_⟩
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hw
      obtain ⟨j, v, hv, rfl⟩ := hw
      exact mul_nonneg (hp0 j) ((ih j).1 v hv)
    · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hw
      obtain ⟨j, v, hv, rfl⟩ := hw
      have hv0 := (ih j).1 v hv
      have hpj : 0 < p j := by
        rcases (hp0 j).eq_or_lt with e | e
        · simp [← e] at hpos
        · exact e
      have hvp : 0 < v.1 := by
        rcases hv0.eq_or_lt with e | e
        · simp [← e] at hpos
        · exact e
      exact (ih j).2 (sep_step hI hS j hpj) v hv hvp
  | forget s t out hl hd hmix ih =>
    refine ⟨fun w hw => by simp at hw; simp [hw], fun hS w hw _ => ?_⟩
    simp at hw; subst hw
    obtain ⟨ι, _, f, g, hfg⟩ := sep_list t.dims out hd ih.1 (ih.2 hS)
    exact ⟨ι, inferInstance, f, g, fun x y hx hy => by rw [hmix, hfg x y hx hy]⟩

end X4ZE

-- ===== ZEC =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P32 (pairOfState)
open scoped Matrix ComplexConjugate ComplexOrder

lemma spec_of {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : X * X = (c : ℂ) • X) : ∀ x ∈ spectrum ℝ X, x = 0 ∨ x = c := by
  have hsa : IsSelfAdjoint X := hX
  have e : cfc (fun x : ℝ => x * x) X = cfc (fun x : ℝ => c * x) X := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) X, cfc_id' ℝ X, cfc_const_mul_id c X, h]
    rw [Complex.coe_smul]
  intro x hx
  have := (eqOn_of_cfc_eq_cfc e : Set.EqOn _ _ _) hx
  simp only at this
  have : x * (x - c) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

lemma vn_scaled {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : X * X = (c : ℂ) • X) : vnEntropy X = -(Real.logb 2 c * X.trace.re) := by
  unfold vnEntropy
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_congr (g := fun x : ℝ => Real.logb 2 c * x)]
  · rw [cfc_const_mul_id _ X, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  · intro x hx
    rcases spec_of hX h x hx with rfl | rfl
    · simp
    · ring

lemma tl_psd {α β : Type*} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) (hv : ‖v‖ = 1) :
    (traceLeft (pureDensity v)).PosSemidef ∧ (traceLeft (pureDensity v)).trace = 1 := by
  set W : Matrix β α ℂ := Matrix.of fun b a => v (a, b)
  have hW : traceLeft (pureDensity v) = W * Wᴴ := by
    ext b b'
    simp [traceLeft, pureDensity, W, Matrix.mul_apply, conjTranspose_apply]
  refine ⟨hW ▸ posSemidef_self_mul_conjTranspose W, ?_⟩
  rw [← unit_sum v hv, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Matrix.trace, traceLeft, pureDensity]

lemma rho_pair (s : Shared) (X Y : RegisterBasis (fun i => Fin (s.dims i))) :
    s.rho X Y = pairOfState s (X 0, X 1) (Y 0, Y 1) := by
  unfold pairOfState
  congr 1 <;> funext i <;> fin_cases i <;> rfl

lemma sep_init (s : Shared) (hs : IsPureShared s) (hz : ent s = 0) : Sep s := by
  obtain ⟨v, hv1, hv⟩ := hs
  have hent : vnEntropy (traceLeft (pureDensity v)) = 0 := by
    have : ent s = vnEntropy (traceLeft (pairOfState s)) := rfl
    rw [this, hv] at hz; exact hz
  obtain ⟨hpsd, htr⟩ := tl_psd v hv1
  obtain ⟨w, hw1, hw⟩ := pure_of_vn hpsd htr hent
  have hsplit := rank1_split (fun b => w b) (unit_sum w hw1) (fun a b => v (a, b)) (fun b b' => by
    have := congrFun (congrFun hw b) b'
    simp only [traceLeft, pureDensity, Matrix.of_apply] at this
    exact this.symm)
  refine ⟨Unit, inferInstance,
    fun _ n => if h : n < s.dims 0 then ∑ b, conj (w b) * v (⟨n, h⟩, b) else 0,
    fun _ n => if h : n < s.dims 1 then w ⟨n, h⟩ else 0, fun x y hx hy => ?_⟩
  rw [se_in s x y hx hy, rho_pair, hv]
  simp only [pureDensity, Matrix.of_apply, Fintype.sum_unique, dif_pos (hx 0), dif_pos (hx 1),
    dif_pos (hy 0), dif_pos (hy 1)]
  rw [hsplit, hsplit (k := ⟨y 0, hy 0⟩)]

lemma ent_of_sep (w : Shared) (hp : IsPureShared w) (hS : Sep w) : ent w = 0 := by
  obtain ⟨v, hv1, hv⟩ := hp
  obtain ⟨ι, _, f, g, hfg⟩ := hS
  set φ : ι → Fin (w.dims 0) × Fin (w.dims 1) → ℂ := fun k a => f k a.1.val * g k a.2.val
  have pk : ∀ a : Fin (w.dims 0) × Fin (w.dims 1), ∀ i, (![a.1.val, a.2.val] : Fin 2 → ℕ) i < w.dims i := by
    intro a i; fin_cases i
    · exact a.1.isLt
    · exact a.2.isLt
  have h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b) := by
    intro a b
    have e1 : v a * conj (v b) = pairOfState w a b := by rw [hv]; rfl
    have e2 : pairOfState w a b = stateEntry w ![a.1.val, a.2.val] ![b.1.val, b.2.val] := by
      rw [se_in w _ _ (pk a) (pk b), rho_pair]; rfl
    rw [e1, e2, hfg _ _ (pk a) (pk b)]
    rfl
  have hU := unit_sum v hv1
  have hsplit := rank1_split v hU φ h
  set c : ι → ℂ := fun k => ∑ b, conj (v b) * φ k b
  obtain ⟨k0, hk0⟩ : ∃ k, c k ≠ 0 := by
    by_contra hc
    push Not at hc
    have : ∀ a, v a * conj (v a) = 0 := fun a => by
      rw [h]; exact Finset.sum_eq_zero fun k _ => by rw [hsplit k a]; simp [c, hc k]
    rw [Finset.sum_eq_zero fun a _ => this a] at hU
    exact zero_ne_one hU
  set F : Fin (w.dims 0) → ℂ := fun a => (c k0)⁻¹ * f k0 a.val
  set G : Fin (w.dims 1) → ℂ := fun b => g k0 b.val
  have hvFG : ∀ a b, v (a, b) = F a * G b := by
    intro a b
    have := hsplit k0 (a, b)
    simp only [F, G]
    rw [show v (a, b) = (c k0)⁻¹ * φ k0 (a, b) by rw [this]; field_simp; rfl]
    simp only [φ]; ring
  set N := ∑ a, F a * conj (F a)
  set M := ∑ b, G b * conj (G b)
  have hNM : N * M = 1 := by
    rw [← hU, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hvFG]; simp only [map_mul]; ring
  set B := traceLeft (pureDensity v)
  have hB : ∀ b b', B b b' = N * (G b * conj (G b')) := by
    intro b b'
    simp only [B, traceLeft, pureDensity, Matrix.of_apply, hvFG, map_mul, N, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hBB : B * B = ((1 : ℝ) : ℂ) • B := by
    ext b b''
    rw [Matrix.mul_apply, Complex.ofReal_one, one_smul]
    simp only [hB]
    calc ∑ b', N * (G b * conj (G b')) * (N * (G b' * conj (G b'')))
        = N * (N * M) * (G b * conj (G b'')) := by
          simp only [M, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b' _ => by ring
      _ = _ := by rw [hNM, mul_one]
  have hent := vn_scaled (tl_psd v hv1).1.1 hBB
  have : ent w = vnEntropy B := by
    show vnEntropy (traceLeft (pairOfState w)) = _
    rw [hv]
  rw [this, hent]; simp

end X4ZE

-- ===== ZESol =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

end QAlgorithms.Papers.Independent.Support50.P42

open QAlgorithms.Papers.Independent.Support50.P42 in
theorem solution (s : Shared) (hs : IsPureShared s) (hzero : ent s=0)
    (out : List (ℝ × Shared)) (hlocal : LocalTree s out) :
    ∀ w∈out, 0<w.1 → IsPureShared w.2 → ent w.2=0 :=
  fun w hw hp hpure => X4ZE.ent_of_sep w.2 hpure
    ((X4ZE.main hlocal).2 (X4ZE.sep_init s hs hzero) w hw hp)

end
