-- Prove2me | solution 1 for ParallelSU2.Reduction.parallel_su2_estimation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T03:35:43.441136+00:00
-- url     : https://prove2.me/submissions/496862a1-e442-4305-9dbb-906802cf4d02

import Mathlib
import Definitions.Def_ParallelSU2_Reduction_Setting
set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix

/-! Spin-(N/2) representation of 2x2 matrices on symmetric tensors, in the
orthonormal weight basis (normalized indicators of weight classes of strings). -/
namespace SymRepAux

def wt {N : ℕ} (a : Fin N → Fin 2) : ℕ := (Finset.univ.filter (fun i => a i = 1)).card

def W (N k : ℕ) : Finset (Fin N → Fin 2) := Finset.univ.filter (fun a => wt a = k)

noncomputable def cc (N k : ℕ) : ℂ := (((Real.sqrt ((W N k).card : ℝ))⁻¹ : ℝ) : ℂ)

def G {N : ℕ} (g : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin N → Fin 2) : ℂ := ∏ i, g (a i) (b i)

noncomputable def S (N : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Matrix.of fun j k => cc N j * cc N k * ∑ a ∈ W N j, ∑ b ∈ W N k, G g a b

lemma wt_le {N : ℕ} (a : Fin N → Fin 2) : wt a ≤ N := by
  unfold wt; exact (Finset.card_filter_le _ _).trans (by simp)

lemma cc_sq (N k : ℕ) (h : (W N k).card ≠ 0) : cc N k * cc N k * ((W N k).card : ℂ) = 1 := by
  unfold cc
  have hpos : (0:ℝ) < (W N k).card := by exact_mod_cast Nat.pos_of_ne_zero h
  have : ((Real.sqrt ((W N k).card : ℝ))⁻¹) * ((Real.sqrt ((W N k).card : ℝ))⁻¹) *
      ((W N k).card : ℝ) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  exact_mod_cast this

lemma card_lt (N k : ℕ) (hk : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).card = k := by
  have h : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).map Fin.valEmbedding =
      Finset.range k := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_range]

lemma W_card_ne_zero (N : ℕ) (k : Fin (N+1)) : (W N k).card ≠ 0 := by
  rw [Finset.card_ne_zero]
  have hf : (Finset.univ.filter fun i : Fin N => (if (i:ℕ) < k then (1 : Fin 2) else 0) = 1) =
      Finset.univ.filter (fun i : Fin N => (i : ℕ) < k) := by
    apply Finset.filter_congr; intro i _; split_ifs with h <;> simp [h]
  refine ⟨fun i => if (i : ℕ) < k then 1 else 0, ?_⟩
  rw [W, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold wt
  rw [hf, card_lt N k (by omega)]

lemma G_mul {N : ℕ} (g h : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin N → Fin 2) :
    G (g * h) a b = ∑ c, G g a c * G h c b := by
  unfold G
  simp only [Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma wt_comp {N : ℕ} (a : Fin N → Fin 2) (σ : Equiv.Perm (Fin N)) : wt (a ∘ σ) = wt a := by
  unfold wt
  exact Finset.card_equiv σ (by intro i; simp)

lemma G_comp {N : ℕ} (g : Matrix (Fin 2) (Fin 2) ℂ) (a c : Fin N → Fin 2)
    (σ : Equiv.Perm (Fin N)) : G g (a ∘ σ) (c ∘ σ) = G g a c := by
  unfold G; exact Equiv.prod_comp σ (fun i => g (a i) (c i))

lemma sumW_left_comp {N : ℕ} (g : Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) (c : Fin N → Fin 2)
    (σ : Equiv.Perm (Fin N)) : ∑ a ∈ W N j, G g a (c ∘ σ) = ∑ a ∈ W N j, G g a c := by
  apply Finset.sum_nbij' (fun a => a ∘ σ.symm) (fun a => a ∘ σ)
  · intro a ha
    have ha' : wt a = j := by simpa [W] using ha
    simpa [W, wt_comp] using ha'
  · intro a ha
    have ha' : wt a = j := by simpa [W] using ha
    simpa [W, wt_comp] using ha'
  · intro a _; funext i; simp
  · intro a _; funext i; simp
  · intro a _
    rw [← G_comp g (a ∘ σ.symm) c σ]
    congr 1; funext i; simp

lemma sumW_right_comp {N : ℕ} (g : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) (c : Fin N → Fin 2)
    (σ : Equiv.Perm (Fin N)) : ∑ b ∈ W N k, G g (c ∘ σ) b = ∑ b ∈ W N k, G g c b := by
  apply Finset.sum_nbij' (fun b => b ∘ σ.symm) (fun b => b ∘ σ)
  · intro a ha
    have ha' : wt a = k := by simpa [W] using ha
    simpa [W, wt_comp] using ha'
  · intro a ha
    have ha' : wt a = k := by simpa [W] using ha
    simpa [W, wt_comp] using ha'
  · intro a _; funext i; simp
  · intro a _; funext i; simp
  · intro b _
    rw [← G_comp g c (b ∘ σ.symm) σ]
    congr 1; funext i; simp

lemma card_zero_eq {N : ℕ} (d : Fin N → Fin 2) :
    (Finset.univ.filter fun i => d i = 0).card = N - wt d := by
  have e := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => d i = 1)
  have hf : (Finset.univ.filter fun i => ¬ d i = 1) = Finset.univ.filter fun i => d i = 0 := by
    apply Finset.filter_congr
    intro i _
    generalize d i = x
    fin_cases x <;> decide
  rw [← hf]
  simp only [Finset.card_univ, Fintype.card_fin] at e
  unfold wt
  omega

lemma exists_perm {N : ℕ} (c c' : Fin N → Fin 2) (h : wt c = wt c') :
    ∃ σ : Equiv.Perm (Fin N), c' = c ∘ σ := by
  have hcard : ∀ x : Fin 2, Fintype.card {i // c' i = x} = Fintype.card {i // c i = x} := by
    intro x
    rw [Fintype.card_subtype, Fintype.card_subtype]
    fin_cases x
    · simp only [Fin.zero_eta]
      rw [card_zero_eq, card_zero_eq, h]
    · show (Finset.univ.filter fun i => c' i = 1).card = (Finset.univ.filter fun i => c i = 1).card
      exact h.symm
  let e : ∀ x : Fin 2, {i // c' i = x} ≃ {i // c i = x} := fun x => Fintype.equivOfCardEq (hcard x)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map e i).symm

lemma sum_const_mul {α : Type*} (s : Finset α) (X Y : α → ℂ)
    (hX : ∀ c ∈ s, ∀ c' ∈ s, X c = X c') (r : ℂ) (hr : s.card ≠ 0 → r * s.card = 1) :
    ∑ c ∈ s, X c * Y c = r * (∑ c ∈ s, X c) * (∑ c ∈ s, Y c) := by
  rcases s.eq_empty_or_nonempty with hs | ⟨c0, hc0⟩
  · simp [hs]
  · have h1 : ∀ c ∈ s, X c = X c0 := fun c hc => hX c hc c0 hc0
    have e1 : ∑ c ∈ s, X c * Y c = X c0 * ∑ c ∈ s, Y c := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c hc => by rw [h1 c hc])
    have e2 : ∑ c ∈ s, X c = s.card * X c0 := by
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have := hr (Finset.card_ne_zero.mpr ⟨c0, hc0⟩)
    rw [e1, e2]
    linear_combination (-(X c0 * ∑ c ∈ s, Y c)) * this

theorem S_mul (N : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℂ) : S N (g * h) = S N g * S N h := by
  ext j k
  simp only [S, Matrix.of_apply, Matrix.mul_apply, G_mul]
  have step : ∑ a ∈ W N j, ∑ b ∈ W N k, ∑ c, G g a c * G h c b =
      ∑ c, (∑ a ∈ W N j, G g a c) * (∑ b ∈ W N k, G h c b) := by
    calc ∑ a ∈ W N j, ∑ b ∈ W N k, ∑ c, G g a c * G h c b
        = ∑ a ∈ W N j, ∑ c, ∑ b ∈ W N k, G g a c * G h c b :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ c, ∑ a ∈ W N j, ∑ b ∈ W N k, G g a c * G h c b := Finset.sum_comm
      _ = _ := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
  have split : ∀ F : (Fin N → Fin 2) → ℂ, ∑ c, F c = ∑ l : Fin (N+1), ∑ c ∈ W N l, F c := by
    intro F
    rw [← Finset.sum_fiberwise Finset.univ
      (fun c => (⟨wt c, Nat.lt_succ_of_le (wt_le c)⟩ : Fin (N+1))) F]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    ext c
    simp [W, Fin.ext_iff]
  rw [step, split, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hX : ∀ c ∈ W N l, ∀ c' ∈ W N l,
      (fun c => ∑ a ∈ W N j, G g a c) c = (fun c => ∑ a ∈ W N j, G g a c) c' := by
    intro c hc c' hc'
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    obtain ⟨σ, rfl⟩ := exists_perm c c' (hc.trans hc'.symm)
    exact (sumW_left_comp g j c σ).symm
  have key := sum_const_mul (W N l) (fun c => ∑ a ∈ W N j, G g a c)
    (fun c => ∑ b ∈ W N k, G h c b) hX (cc N l * cc N l) (fun hh => cc_sq N l hh)
  beta_reduce at key
  rw [key, Finset.sum_comm (s := W N j)]
  ring

theorem S_one (N : ℕ) : S N 1 = 1 := by
  ext j k
  have hG : ∀ a b : Fin N → Fin 2,
      G (1 : Matrix (Fin 2) (Fin 2) ℂ) a b = if a = b then 1 else 0 := by
    intro a b; unfold G; simp only [Matrix.one_apply]; rw [Fintype.prod_boole]
    by_cases hab : a = b
    · simp [hab]
    · rw [if_neg, if_neg hab]; intro hh; exact hab (funext hh)
  simp only [S, Matrix.of_apply, hG, Finset.sum_ite_eq, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl]
    have : ∑ a ∈ W N j, (if a ∈ W N j then (1:ℂ) else 0) = (W N j).card := by
      rw [Finset.sum_ite_mem, Finset.inter_self]; simp
    rw [this]; exact cc_sq N j (W_card_ne_zero N j)
  · rw [if_neg hjk]
    rw [Finset.sum_eq_zero, mul_zero]
    intro a ha
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [if_neg]; intro hb; exact hjk (Fin.ext (ha.symm.trans hb))

theorem S_conjTranspose (N : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : S N gᴴ = (S N g)ᴴ := by
  ext j k
  have hc : ∀ m, star (cc N m) = cc N m := fun m => by simp [cc, Complex.conj_ofReal]
  simp only [S, Matrix.of_apply, Matrix.conjTranspose_apply, G, star_mul', star_sum, star_prod, hc]
  rw [Finset.sum_comm]
  ring

theorem S_continuous (N : ℕ) : Continuous (fun g : Matrix (Fin 2) (Fin 2) ℂ => S N g) := by
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [S, Matrix.of_apply, G]
  fun_prop

section trace

lemma G_upper_offdiag {N : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M 1 0 = 0)
    (a b : Fin N → Fin 2) (hw : wt a = wt b) (hab : a ≠ b) : G M a b = 0 := by
  by_contra hne
  apply hab
  have hnz : ∀ i, ¬ (a i = 1 ∧ b i = 0) := by
    rintro i ⟨h1, h0⟩
    apply hne
    unfold G
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [h1, h0, hM]
  have hsub : (Finset.univ.filter fun i => a i = 1) ⊆ Finset.univ.filter fun i => b i = 1 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h := hnz i
    rw [hi] at h
    revert h
    generalize b i = y
    fin_cases y <;> decide
  have heq := Finset.eq_of_subset_of_card_le hsub (by unfold wt at hw; omega)
  funext i
  have hi : (a i = 1 ↔ b i = 1) := by
    have h := congrArg (fun s => i ∈ s) heq
    simpa using h
  revert hi
  generalize a i = x
  generalize b i = y
  fin_cases x <;> fin_cases y <;> decide

lemma G_diag {N : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin N → Fin 2) :
    G M a a = M 0 0 ^ (N - wt a) * M 1 1 ^ wt a := by
  unfold G
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => a i = 1)]
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => a i = 1), M (a i) (a i) = M 1 1 := by
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  have h0 : ∀ i ∈ Finset.univ.filter (fun i => ¬ a i = 1), M (a i) (a i) = M 0 0 := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have : a i = 0 := by revert h; generalize a i = x; fin_cases x <;> decide
    rw [this]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h0, Finset.prod_const, Finset.prod_const]
  have e := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => a i = 1)
  simp only [Finset.card_univ, Fintype.card_fin] at e
  have : (Finset.univ.filter (fun i => ¬ a i = 1)).card = N - wt a := by unfold wt; omega
  rw [this]; unfold wt; ring

lemma S_upper_diag (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M 1 0 = 0) (k : Fin (N+1)) :
    S N M k k = M 0 0 ^ (N - k) * M 1 1 ^ (k : ℕ) := by
  simp only [S, Matrix.of_apply]
  have hin : ∀ a ∈ W N k, ∑ b ∈ W N k, G M a b = M 0 0 ^ (N - k) * M 1 1 ^ (k : ℕ) := by
    intro a ha
    have ha' : wt a = k := by simpa [W] using ha
    rw [Finset.sum_eq_single a]
    · rw [G_diag, ha']
    · intro b hb hba
      have hb' : wt b = k := by simpa [W] using hb
      exact G_upper_offdiag M hM a b (ha'.trans hb'.symm) (Ne.symm hba)
    · intro h; exact absurd ha h
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  linear_combination (M 0 0 ^ (N - k) * M 1 1 ^ (k : ℕ)) * cc_sq N k (W_card_ne_zero N k)

noncomputable def hsum (N : ℕ) (x y : ℂ) : ℂ := ∑ k ∈ Finset.range (N+1), x ^ (N - k) * y ^ k

lemma trace_S_upper (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M 1 0 = 0) :
    (S N M).trace = hsum N (M 0 0) (M 1 1) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, S_upper_diag N M hM]
  rw [Fin.sum_univ_eq_sum_range (fun k => M 0 0 ^ (N - k) * M 1 1 ^ k)]
  rfl

lemma hsum_succ (N : ℕ) (x y : ℂ) : hsum (N+1) x y = y * hsum N x y + x ^ (N+1) := by
  unfold hsum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    have : N + 1 - (k + 1) = N - k := by omega
    rw [this, pow_succ]; ring
  · simp

lemma hsum_cheb (x y : ℂ) (hxy : x * y = 1) (N : ℕ) :
    hsum N x y = (Polynomial.Chebyshev.U ℂ (N : ℤ)).eval ((x + y) / 2) := by
  have key : ∀ n : ℕ, hsum n x y = (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval ((x + y) / 2) ∧
      hsum (n+1) x y = (Polynomial.Chebyshev.U ℂ ((n + 1 : ℕ) : ℤ)).eval ((x + y) / 2) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp [hsum]
      · simp [hsum, Finset.sum_range_succ, Polynomial.Chebyshev.U_one]
        try ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨h0, h1⟩ := ih
      have r := Polynomial.Chebyshev.U_add_two ℂ (n : ℤ)
      have e2 : ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
      have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [e2, r]
      rw [e1] at h1
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      rw [← h1, ← h0, hsum_succ (n+1)]
      linear_combination (-x) * hsum_succ n x y - hsum n x y * hxy
  exact (key N).1

lemma su2_d (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : star g * g = 1) (hd : g.det = 1) :
    g 1 1 = conj (g 0 0) := by
  have e00 := congrFun (congrFun hu 0) 0
  have e01 := congrFun (congrFun hu 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at e00 e01
  rw [Matrix.det_fin_two] at hd
  linear_combination (-(g 1 1)) * e00 + (g 1 0) * e01 + conj (g 0 0) * hd

lemma su2_trace_real (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : star g * g = 1) (hd : g.det = 1) :
    ((g.trace.re : ℝ) : ℂ) = g.trace := by
  rw [Matrix.trace_fin_two, su2_d g hu hd]
  apply Complex.ext <;> simp

lemma exists_upper (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℂ, IsUnit P.det ∧ (P⁻¹ * g * P) 1 0 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (g.trace ^ 2 - 4 * g.det)
  set ev : ℂ := (g.trace + s) / 2 with hev
  have hdet : (g - ev • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    rw [Matrix.det_fin_two]
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hs
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      mul_one, mul_zero, sub_zero]
    rw [hev, Matrix.trace_fin_two]
    linear_combination (-1/4 : ℂ) * hs
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] at h0 h1
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![v 0, -conj (v 1); v 1, conj (v 0)]
  have hPdet : P.det ≠ 0 := by
    intro hz
    apply hv0
    simp only [P, Matrix.det_fin_two_of] at hz
    have hz' : ((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ) = 0 := by
      push_cast
      rw [← Complex.mul_conj, ← Complex.mul_conj]
      linear_combination hz
    have hr : Complex.normSq (v 0) + Complex.normSq (v 1) = 0 := by exact_mod_cast hz'
    have a0 := Complex.normSq_nonneg (v 0)
    have a1 := Complex.normSq_nonneg (v 1)
    have b0 : v 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have b1 : v 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    funext i; fin_cases i <;> simp [b0, b1]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hcol : ∀ i, (g * P) i 0 = ev * P i 0 := by
    intro i
    fin_cases i
    · simp [Matrix.mul_apply, Fin.sum_univ_two, P]; linear_combination h0
    · simp [Matrix.mul_apply, Fin.sum_univ_two, P]; linear_combination h1
  refine ⟨P, hPu, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hinv : (P⁻¹ * P) 1 0 = 0 := by rw [Matrix.nonsing_inv_mul P hPu]; simp
  rw [Matrix.mul_apply] at hinv
  calc ∑ x, P⁻¹ 1 x * (g * P) x 0 = ev * ∑ x, P⁻¹ 1 x * P x 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by rw [hcol]; ring)
    _ = 0 := by rw [hinv, mul_zero]

lemma U_real_cast (n : ℤ) (r : ℝ) :
    (((Polynomial.Chebyshev.U ℝ n).eval r : ℝ) : ℂ) = (Polynomial.Chebyshev.U ℂ n).eval (r : ℂ) := by
  rw [← Polynomial.Chebyshev.map_U (algebraMap ℝ ℂ), Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) r).symm

theorem trace_S_su2 (N : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : star g * g = 1)
    (hd : g.det = 1) :
    (S N g).trace = (((Polynomial.Chebyshev.U ℝ (N : ℤ)).eval (g.trace.re / 2) : ℝ) : ℂ) := by
  obtain ⟨P, hPu, hT⟩ := exists_upper g
  set T := P⁻¹ * g * P with hTdef
  have hg : g = P * T * P⁻¹ := by
    rw [hTdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPu,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPu, Matrix.mul_one]
  have htr : (S N g).trace = (S N T).trace := by
    conv_lhs => rw [hg]
    rw [S_mul, S_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← S_mul,
      Matrix.nonsing_inv_mul P hPu, S_one, Matrix.one_mul]
  have htrT : T.trace = g.trace := by
    rw [hTdef, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPu,
      Matrix.one_mul]
  have hdetT : T.det = 1 := by
    rw [hTdef, Matrix.det_mul, Matrix.det_mul, hd, mul_one, Matrix.det_nonsing_inv,
      Ring.inverse_mul_cancel _ hPu]
  rw [htr, trace_S_upper N T hT]
  rw [Matrix.det_fin_two, hT, mul_zero, sub_zero] at hdetT
  rw [hsum_cheb _ _ hdetT, U_real_cast]
  congr 1
  rw [Matrix.trace_fin_two] at htrT
  push_cast
  rw [su2_trace_real g hu hd, ← htrT]

end trace

section irred

lemma G_offdiag_zero {N : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (h10 : M 1 0 = 0) (h01 : M 0 1 = 0)
    (a b : Fin N → Fin 2) (hab : a ≠ b) : G M a b = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  unfold G
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  revert hi
  generalize a i = x
  generalize b i = y
  fin_cases x <;> fin_cases y <;> simp [h10, h01]

lemma S_diagmat (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (h10 : M 1 0 = 0) (h01 : M 0 1 = 0)
    (j k : Fin (N+1)) :
    S N M j k = if j = k then M 0 0 ^ (N - k) * M 1 1 ^ (k : ℕ) else 0 := by
  split_ifs with hjk
  · subst hjk; exact S_upper_diag N M h10 j
  · simp only [S, Matrix.of_apply]
    rw [Finset.sum_eq_zero, mul_zero]
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    apply G_offdiag_zero M h10 h01
    rintro rfl
    have ha' : wt a = j := by simpa [W] using ha
    have hb' : wt a = k := by simpa [W] using hb
    exact hjk (Fin.ext (ha'.symm.trans hb'))

lemma S_diagmat_mulVec (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (h10 : M 1 0 = 0)
    (h01 : M 0 1 = 0) (v : Fin (N+1) → ℂ) :
    S N M *ᵥ v = fun j : Fin (N+1) => (M 0 0 ^ (N - (j : ℕ)) * M 1 1 ^ (j : ℕ)) * v j := by
  funext j
  simp only [Matrix.mulVec, dotProduct, S_diagmat N M h10 h01]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj; simp [Ne.symm hkj]
  · simp

lemma sep {n : ℕ} (μ : Fin n → ℂ) (hμ : Function.Injective μ) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ v ∈ V, (fun j => μ j * v j) ∈ V) (v : Fin n → ℂ) (hv : v ∈ V) (k : Fin n)
    (hk : v k ≠ 0) : Pi.single k 1 ∈ V := by
  have step : ∀ J : Finset (Fin n), (fun i => (∏ j ∈ J, (μ i - μ j)) * v i) ∈ V := by
    intro J
    refine Finset.induction_on J ?_ ?_
    · simpa using hv
    · intro j J hj ih
      have h2 := V.sub_mem (hV _ ih) (V.smul_mem (μ j) ih)
      convert h2 using 1
      funext i
      simp only [Finset.prod_insert hj, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hw := step (Finset.univ.erase k)
  set c := ∏ j ∈ Finset.univ.erase k, (μ k - μ j) with hcdef
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun j hj => sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hμ h).symm))
  have heq : (fun i => (∏ j ∈ Finset.univ.erase k, (μ i - μ j)) * v i) =
      (c * v k) • (Pi.single k 1 : Fin n → ℂ) := by
    funext i
    by_cases hik : i = k
    · subst hik; simp [hcdef]
    · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) (sub_self _)]
      simp [Pi.single_apply, hik]
  rw [heq] at hw
  have := V.smul_mem (c * v k)⁻¹ hw
  rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hk), one_smul] at this

lemma prod_split {N : ℕ} (f : Fin 2 → ℂ) (b : Fin N → Fin 2) :
    ∏ i, f (b i) = f 0 ^ (N - wt b) * f 1 ^ wt b := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => b i = 1)]
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => b i = 1), f (b i) = f 1 := by
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  have h0 : ∀ i ∈ Finset.univ.filter (fun i => ¬ b i = 1), f (b i) = f 0 := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    have : b i = 0 := by revert h; generalize b i = x; fin_cases x <;> decide
    rw [this]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h0, Finset.prod_const, Finset.prod_const]
  have e := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun i => b i = 1)
  simp only [Finset.card_univ, Fintype.card_fin] at e
  have : (Finset.univ.filter (fun i => ¬ b i = 1)).card = N - wt b := by unfold wt; omega
  rw [this]; unfold wt; ring

lemma W_zero_eq {N : ℕ} (a : Fin N → Fin 2) (ha : a ∈ W N 0) : a = 0 := by
  have h0 : wt a = 0 := by simpa [W] using ha
  unfold wt at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  funext i
  have h := h0 (Finset.mem_univ i)
  show a i = 0
  revert h
  generalize a i = x
  fin_cases x <;> decide

lemma zero_mem_W (N : ℕ) : (0 : Fin N → Fin 2) ∈ W N 0 := by
  simp [W, wt]

lemma sum_W0 (N : ℕ) (F : (Fin N → Fin 2) → ℂ) : ∑ a ∈ W N 0, F a = F 0 := by
  rw [Finset.sum_eq_single 0]
  · intro a ha hne; exact absurd (W_zero_eq a ha) hne
  · intro h; exact absurd (zero_mem_W N) h

lemma S_row0 (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin (N+1)) :
    S N M 0 k = cc N 0 * cc N k * (((W N k).card : ℂ) * (M 0 0 ^ (N - k) * M 0 1 ^ (k : ℕ))) := by
  simp only [S, Matrix.of_apply, Fin.val_zero, sum_W0]
  have : ∀ b ∈ W N k, G M 0 b = M 0 0 ^ (N - k) * M 0 1 ^ (k : ℕ) := by
    intro b hb
    have hb' : wt b = k := by simpa [W] using hb
    unfold G
    simp only [Pi.zero_apply]
    rw [prod_split (M 0) b, hb']
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

lemma S_col0 (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin (N+1)) :
    S N M j 0 = cc N j * cc N 0 * (((W N j).card : ℂ) * (M 0 0 ^ (N - j) * M 1 0 ^ (j : ℕ))) := by
  simp only [S, Matrix.of_apply, Fin.val_zero, sum_W0]
  have : ∀ a ∈ W N j, G M a 0 = M 0 0 ^ (N - j) * M 1 0 ^ (j : ℕ) := by
    intro a ha
    have ha' : wt a = j := by simpa [W] using ha
    show ∏ i, M (a i) 0 = _
    have := prod_split (fun x => M x 0) a
    rw [this, ha']
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

theorem S_irred_of (N : ℕ) (V : Submodule ℂ (Fin (N+1) → ℂ)) (D R : Matrix (Fin 2) (Fin 2) ℂ)
    (hD : ∀ v ∈ V, S N D *ᵥ v ∈ V) (hR : ∀ v ∈ V, S N R *ᵥ v ∈ V)
    (h10 : D 1 0 = 0) (h01 : D 0 1 = 0)
    (hinj : Function.Injective (fun k : Fin (N+1) => D 0 0 ^ (N - k) * D 1 1 ^ (k : ℕ)))
    (r00 : R 0 0 ≠ 0) (r01 : R 0 1 ≠ 0) (r10 : R 1 0 ≠ 0) : V = ⊥ ∨ V = ⊤ := by
  have hsep : ∀ v ∈ V, ∀ k, v k ≠ 0 → Pi.single k 1 ∈ V := by
    intro v hv k hk
    refine sep _ hinj V (fun w hw => ?_) v hv k hk
    have := hD w hw
    rwa [S_diagmat_mulVec N D h10 h01] at this
  have hcc : ∀ m : ℕ, m ≤ N → cc N m ≠ 0 := by
    intro m hm h
    have := cc_sq N m (W_card_ne_zero N ⟨m, by omega⟩)
    rw [h] at this; simp at this
  have hcard : ∀ m : ℕ, m ≤ N → ((W N m).card : ℂ) ≠ 0 := fun m hm => by
    exact_mod_cast W_card_ne_zero N ⟨m, by omega⟩
  have hsingle : ∀ k, (S N R *ᵥ Pi.single k 1) = fun j => S N R j k := by
    intro k; funext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  by_cases hbot : V = ⊥
  · left; exact hbot
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv0
  have ek := hsep v hv k hk
  have w := hR _ ek
  rw [hsingle] at w
  have e0 := hsep _ w 0 (by
    show S N R 0 k ≠ 0
    rw [S_row0]
    exact mul_ne_zero (mul_ne_zero (hcc 0 (Nat.zero_le _)) (hcc k k.is_le))
      (mul_ne_zero (hcard k k.is_le) (mul_ne_zero (pow_ne_zero _ r00) (pow_ne_zero _ r01))))
  have u := hR _ e0
  rw [hsingle] at u
  have all : ∀ j, Pi.single j 1 ∈ V := fun j => hsep _ u j (by
    show S N R j 0 ≠ 0
    rw [S_col0]
    exact mul_ne_zero (mul_ne_zero (hcc j j.is_le) (hcc 0 (Nat.zero_le _)))
      (mul_ne_zero (hcard j j.is_le) (mul_ne_zero (pow_ne_zero _ r00) (pow_ne_zero _ r10))))
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine V.sum_mem (fun j _ => ?_)
  have h : Pi.single j (x j) = x j • (Pi.single j (1:ℂ) : Fin (N+1) → ℂ) := by
    funext i; by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  rw [h]; exact V.smul_mem _ (all j)

end irred

end SymRepAux

namespace SymRepAux
section spin
open ParallelSU2.Reduction QAlgorithms.Papers.Independent.Next46.P36

noncomputable def th (N : ℕ) : ℝ := Real.pi / ((N : ℝ) + 1)

noncomputable def Dm (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((th N : ℂ) * Complex.I), 0; 0, Complex.exp (-((th N : ℂ) * Complex.I))]

noncomputable def rr : ℝ := (Real.sqrt 2)⁻¹

noncomputable def Rm : Matrix (Fin 2) (Fin 2) ℂ := !![(rr : ℂ), -(rr : ℂ); (rr : ℂ), (rr : ℂ)]

lemma rr_sq : (rr : ℂ) * rr = 1 / 2 := by
  have h : rr * rr = 1 / 2 := by
    rw [rr, ← sq, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  rw [← Complex.ofReal_mul, h]; push_cast; ring

lemma Rm_mem : Rm ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have hc : star (rr : ℂ) = rr := Complex.conj_ofReal _
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Rm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc] <;>
      linear_combination 2 * rr_sq
  · rw [Matrix.det_fin_two]; simp [Rm]; linear_combination 2 * rr_sq

lemma Dm_mem (N : ℕ) : Dm N ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have hc : star (th N : ℂ) = th N := Complex.conj_ofReal _
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have e1 : Complex.exp ((th N : ℂ) * Complex.I) * Complex.exp (-((th N : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Dm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, ← Complex.exp_conj,
        ← Complex.exp_add]
  · rw [Matrix.det_fin_two]; simp [Dm, e1]

lemma Dm_pow (N : ℕ) (k : Fin (N+1)) :
    Dm N 0 0 ^ (N - k) * Dm N 1 1 ^ (k : ℕ) =
      Complex.exp (((((N - k : ℕ) : ℝ) - (k : ℝ)) * th N : ℝ) * Complex.I) := by
  simp only [Dm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma Dm_inj (N : ℕ) :
    Function.Injective (fun k : Fin (N+1) => Dm N 0 0 ^ (N - k) * Dm N 1 1 ^ (k : ℕ)) := by
  intro a b h
  simp only [Dm_pow] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hn' := congrArg Complex.im hn
  simp at hn'
  have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.mp a.2
  have hb : (b : ℕ) ≤ N := Nat.lt_succ_iff.mp b.2
  set xa : ℝ := ((N - a : ℕ) : ℝ) - (a : ℝ) with hxa
  set xb : ℝ := ((N - b : ℕ) : ℝ) - (b : ℝ) with hxb
  have hθ : th N * ((N : ℝ) + 1) = Real.pi := by
    rw [th]; field_simp
  have key : (xa - xb) * Real.pi = (2 * n * ((N : ℝ) + 1)) * Real.pi := by
    linear_combination ((N : ℝ) + 1) * hn' - (xa - xb) * hθ
  have key2 := mul_right_cancel₀ Real.pi_ne_zero key
  rw [hxa, hxb, Nat.cast_sub ha, Nat.cast_sub hb] at key2
  have kz : ((b : ℤ) - a) = n * ((N : ℤ) + 1) := by
    have : ((b : ℝ) - a) = (n : ℝ) * ((N : ℝ) + 1) := by linarith
    exact_mod_cast this
  have hbz : (b : ℤ) ≤ N := by exact_mod_cast hb
  have haz : (a : ℤ) ≤ N := by exact_mod_cast ha
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have : n ≤ -1 := by omega
      nlinarith
    · exact h
    · have : 1 ≤ n := by omega
      nlinarith
  subst hn0
  apply Fin.ext; omega

lemma coe_su2_mul (g h : SU2) : ((g * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) := rfl
lemma coe_su2_one : ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl

noncomputable def spinIrrep (N : ℕ) : BasedIrrep SU2 where
  dim := N + 1
  positive := Nat.succ_pos N
  matrix g := S N (g : Matrix (Fin 2) (Fin 2) ℂ)
  one := by rw [coe_su2_one, S_one]
  mul g h := by rw [coe_su2_mul, S_mul]
  unitary g := by
    have hu := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
    have h1 := Matrix.mem_unitaryGroup_iff'.mp hu
    have h2 := Matrix.mem_unitaryGroup_iff.mp hu
    rw [Matrix.star_eq_conjTranspose] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [← S_conjTranspose, ← S_mul, h1, S_one]
    · rw [← S_conjTranspose, ← S_mul, h2, S_one]
  continuous := (S_continuous N).comp continuous_subtype_val
  irreducible V hV := by
    refine S_irred_of N V (Dm N) Rm (fun v hv => hV ⟨Dm N, Dm_mem N⟩ v hv)
      (fun v hv => hV ⟨Rm, Rm_mem⟩ v hv) (by simp [Dm]) (by simp [Dm]) (Dm_inj N)
      ?_ ?_ ?_ <;> simp [Rm, rr]

lemma spinIrrep_trace (N : ℕ) (g : SU2) :
    ((spinIrrep N).matrix g).trace = (weylCharacter (N + 1) g : ℂ) := by
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp g.2)
  show (S N (g : Matrix (Fin 2) (Fin 2) ℂ)).trace = _
  rw [trace_S_su2 N _ (Matrix.mem_unitaryGroup_iff'.mp hu.1) hu.2, weylCharacter]
  congr 4; push_cast; ring

theorem spin_family_exists (d : ℕ) :
    ∃ D : Fin d → BasedIrrep SU2, IsSpinFamily D := by
  refine ⟨fun k => spinIrrep (2 * k.val + 1), fun k => ⟨?_, fun g => ?_⟩⟩
  · show 2 * k.val + 1 + 1 = _; ring
  · rw [spinIrrep_trace, show 2 * k.val + 1 + 1 = 2 * (k.val + 1) by ring]

end spin
end SymRepAux
open MeasureTheory Matrix
open scoped ComplexConjugate

namespace SchurAux
open QAlgorithms.Papers.Independent.Next46.P36

section alg
variable {G : Type*} [Group G] [TopologicalSpace G]

lemma eq_zero_of_ker_top {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ)
    (h : LinearMap.ker (Matrix.mulVecLin C) = ⊤) : C = 0 := by
  ext i j
  have hv : Pi.single j (1 : ℂ) ∈ LinearMap.ker (Matrix.mulVecLin C) := by rw [h]; trivial
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  have := congrFun hv i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

lemma ker_inv (A B : BasedIrrep G) (C : Matrix (Fin A.dim) (Fin B.dim) ℂ)
    (hC : ∀ g, A.matrix g * C = C * B.matrix g) :
    LinearMap.ker (Matrix.mulVecLin C) = ⊥ ∨ LinearMap.ker (Matrix.mulVecLin C) = ⊤ := by
  apply B.irreducible
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hC, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma range_inv (A B : BasedIrrep G) (C : Matrix (Fin A.dim) (Fin B.dim) ℂ)
    (hC : ∀ g, A.matrix g * C = C * B.matrix g) :
    LinearMap.range (Matrix.mulVecLin C) = ⊥ ∨ LinearMap.range (Matrix.mulVecLin C) = ⊤ := by
  apply A.irreducible
  intro g v hv
  obtain ⟨w, rfl⟩ := hv
  exact ⟨B.matrix g *ᵥ w, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hC]⟩

theorem schur_zero (A B : BasedIrrep G) (C : Matrix (Fin A.dim) (Fin B.dim) ℂ)
    (hC : ∀ g, A.matrix g * C = C * B.matrix g) (hd : A.dim ≠ B.dim) : C = 0 := by
  rcases ker_inv A B C hC with hk | hk
  · rcases range_inv A B C hC with hr | hr
    · ext i j
      have hv : Matrix.mulVecLin C (Pi.single j 1) ∈ (⊥ : Submodule ℂ (Fin A.dim → ℂ)) :=
        hr ▸ LinearMap.mem_range_self _ _
      rw [Submodule.mem_bot, Matrix.mulVecLin_apply] at hv
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    · exfalso
      have h1 : B.dim ≤ A.dim := by
        have := LinearMap.finrank_le_finrank_of_injective (f := Matrix.mulVecLin C)
          (LinearMap.ker_eq_bot.mp hk)
        simpa using this
      have h2 : A.dim ≤ B.dim := by
        have := LinearMap.finrank_range_le (Matrix.mulVecLin C)
        rw [hr, finrank_top] at this
        simpa using this
      omega
  · exact eq_zero_of_ker_top C hk

theorem schur_scalar (A : BasedIrrep G) (C : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hC : ∀ g, A.matrix g * C = C * A.matrix g) : ∃ c : ℂ, C = c • (1 : Matrix _ _ ℂ) := by
  have : Nonempty (Fin A.dim) := ⟨⟨0, A.positive⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin C)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hC' : ∀ g, A.matrix g * (C - c • 1) = (C - c • 1) * A.matrix g := by
    intro g; rw [Matrix.mul_sub, Matrix.sub_mul, hC, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  rcases ker_inv A A (C - c • 1) hC' with hk | hk
  · exfalso
    have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin (C - c • 1)) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      have := hv.apply_eq_smul
      rw [Matrix.mulVecLin_apply] at this
      rw [this, sub_self]
    rw [hk, Submodule.mem_bot] at hmem
    exact hv.2 hmem
  · exact sub_eq_zero.mp (eq_zero_of_ker_top _ hk)

lemma rep_inv (B : BasedIrrep G) (g : G) : B.matrix g⁻¹ = (B.matrix g)ᴴ := by
  have h1 : B.matrix g⁻¹ * B.matrix g = 1 := by rw [← B.mul, inv_mul_cancel, B.one]
  have h2 := (B.unitary g).2
  calc B.matrix g⁻¹ = B.matrix g⁻¹ * (B.matrix g * (B.matrix g)ᴴ) := by rw [h2, Matrix.mul_one]
    _ = (B.matrix g)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma entry_single {a b m n : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (M : Matrix m a ℂ) (N : Matrix b n ℂ) (x : a) (y : b) (i : m) (j : n) :
    (M * Matrix.single x y (1 : ℂ) * N) i j = M i x * N y j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq]

end alg

section integ
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

lemma integrable_of_cont {f : G → ℂ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

lemma int_mul_left {m n p : Type*} [Fintype n] (M : Matrix m n ℂ) (F : G → Matrix n p ℂ)
    (hF : Continuous F) (i : m) (j : p) :
    ∫ h, (M * F h) i j ∂μ = ∑ k, M i k * ∫ h, F h k j ∂μ := by
  simp only [Matrix.mul_apply]
  rw [integral_finsetSum]
  · congr 1; ext k; exact integral_const_mul _ _
  · intro k _; exact (integrable_of_cont μ (hF.matrix_elem k j)).const_mul _

lemma int_mul_right {m n p : Type*} [Fintype n] (M : Matrix n p ℂ) (F : G → Matrix m n ℂ)
    (hF : Continuous F) (i : m) (j : p) :
    ∫ h, (F h * M) i j ∂μ = ∑ k, (∫ h, F h i k ∂μ) * M k j := by
  simp only [Matrix.mul_apply]
  rw [integral_finsetSum]
  · congr 1; ext k; exact integral_mul_const _ _
  · intro k _; exact (integrable_of_cont μ (hF.matrix_elem i k)).mul_const _

noncomputable def avg (A B : BasedIrrep G) (E : Matrix (Fin A.dim) (Fin B.dim) ℂ) :
    Matrix (Fin A.dim) (Fin B.dim) ℂ :=
  Matrix.of fun i j => ∫ h, (A.matrix h * E * (B.matrix h)ᴴ) i j ∂μ

lemma avg_cont (A B : BasedIrrep G) (E : Matrix (Fin A.dim) (Fin B.dim) ℂ) :
    Continuous fun h => A.matrix h * E * (B.matrix h)ᴴ :=
  (A.continuous.matrix_mul continuous_const).matrix_mul B.continuous.matrix_conjTranspose

variable [μ.IsMulLeftInvariant]

theorem avg_intertwine (A B : BasedIrrep G) (E : Matrix (Fin A.dim) (Fin B.dim) ℂ) (g : G) :
    A.matrix g * avg μ A B E = avg μ A B E * B.matrix g := by
  have hF := avg_cont A B E
  ext i j
  have L : (A.matrix g * avg μ A B E) i j =
      ∫ h, (A.matrix g * (A.matrix h * E * (B.matrix h)ᴴ)) i j ∂μ := by
    rw [int_mul_left μ _ _ hF, Matrix.mul_apply]; rfl
  have R : (avg μ A B E * B.matrix g) i j =
      ∫ h, ((A.matrix h * E * (B.matrix h)ᴴ) * B.matrix g) i j ∂μ := by
    rw [int_mul_right μ _ _ hF, Matrix.mul_apply]; rfl
  rw [L, R]
  have e1 : ∀ h, A.matrix g * (A.matrix h * E * (B.matrix h)ᴴ) =
      A.matrix (g * h) * E * (B.matrix h)ᴴ := by
    intro h; rw [A.mul]; simp only [Matrix.mul_assoc]
  have e2 : ∀ h, (A.matrix h * E * (B.matrix h)ᴴ) * B.matrix g =
      A.matrix h * E * (B.matrix (g⁻¹ * h))ᴴ := by
    intro h; rw [B.mul, Matrix.conjTranspose_mul, rep_inv, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  simp_rw [e1, e2]
  rw [← integral_mul_left_eq_self (fun h => (A.matrix h * E * (B.matrix (g⁻¹ * h))ᴴ) i j) g]
  simp only [inv_mul_cancel_left]

theorem avg_trace (A : BasedIrrep G) (E : Matrix (Fin A.dim) (Fin A.dim) ℂ) :
    (avg μ A A E).trace = E.trace := by
  have hF := avg_cont A A E
  have h1 : (avg μ A A E).trace = ∫ h, (A.matrix h * E * (A.matrix h)ᴴ).trace ∂μ := by
    simp only [Matrix.trace]
    rw [integral_finsetSum]
    · rfl
    · intro k _; exact integrable_of_cont μ (hF.matrix_elem k k)
  rw [h1]
  have h2 : ∀ h, (A.matrix h * E * (A.matrix h)ᴴ).trace = E.trace := by
    intro h
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, (A.unitary h).1, Matrix.one_mul]
  simp_rw [h2]
  simp

/-- Schur orthogonality, different dimensions. -/
theorem orth_ne (A B : BasedIrrep G) (hd : A.dim ≠ B.dim) (i i' : Fin A.dim) (m m' : Fin B.dim) :
    ∫ h, A.matrix h i i' * conj (B.matrix h m m') ∂μ = 0 := by
  have h0 := schur_zero A B (avg μ A B (Matrix.single i' m' (1 : ℂ))) (avg_intertwine μ A B _) hd
  have := congrFun (congrFun h0 i) m
  simp only [avg, Matrix.of_apply, Matrix.zero_apply, entry_single, Matrix.conjTranspose_apply,
    Complex.star_def] at this
  exact this

/-- Schur orthogonality, same irrep. -/
theorem orth_eq (A : BasedIrrep G) (i i' m m' : Fin A.dim) :
    ∫ h, A.matrix h i i' * conj (A.matrix h m m') ∂μ =
      if i = m ∧ i' = m' then 1 / (A.dim : ℂ) else 0 := by
  obtain ⟨c, hc⟩ := schur_scalar A (avg μ A A (Matrix.single i' m' (1 : ℂ))) (avg_intertwine μ A A _)
  have htr := avg_trace μ A (Matrix.single i' m' (1 : ℂ))
  rw [hc] at htr
  have hdim : (A.dim : ℂ) ≠ 0 := by exact_mod_cast A.positive.ne'
  have := congrFun (congrFun hc i) m
  simp only [avg, Matrix.of_apply, entry_single, Matrix.conjTranspose_apply,
    Complex.star_def] at this
  have htr' : c * (A.dim : ℂ) = if i' = m' then 1 else 0 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
    rw [htr]
    split_ifs with hh
    · subst hh; simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne, hh]
  rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h1 : i = m <;> by_cases h2 : i' = m' <;>
    simp only [h1, h2, if_true, if_false, and_true, and_false, true_and, false_and, mul_one,
      mul_zero] at htr' ⊢
  · field_simp; linear_combination htr'
  · exact (mul_eq_zero.mp htr').resolve_right hdim

lemma prod_int (A B : BasedIrrep G) (i : Fin A.dim) (m : Fin B.dim) :
    Integrable (fun h => A.matrix h i i * conj (B.matrix h m m)) μ :=
  integrable_of_cont μ ((A.continuous.matrix_elem i i).mul
    (Complex.continuous_conj.comp (B.continuous.matrix_elem m m)))

lemma trace_prod (A B : BasedIrrep G) (h : G) :
    (A.matrix h).trace * conj ((B.matrix h).trace) =
      ∑ i, ∑ m, A.matrix h i i * conj (B.matrix h m m) := by
  simp only [Matrix.trace, Matrix.diag, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem char_orth_self (A : BasedIrrep G) :
    ∫ h, (A.matrix h).trace * conj ((A.matrix h).trace) ∂μ = 1 := by
  simp_rw [trace_prod]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ => prod_int μ A A i m))]
  rw [Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun m _ => prod_int μ A A i m))]
  simp only [orth_eq, and_self]
  have hdim : (A.dim : ℂ) ≠ 0 := by exact_mod_cast A.positive.ne'
  simp [Finset.sum_ite_eq]
  field_simp

theorem char_orth_ne (A B : BasedIrrep G) (hd : A.dim ≠ B.dim) :
    ∫ h, (A.matrix h).trace * conj ((B.matrix h).trace) ∂μ = 0 := by
  simp_rw [trace_prod]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ => prod_int μ A B i m))]
  rw [Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun m _ => prod_int μ A B i m))]
  simp only [orth_ne μ A B hd, Finset.sum_const_zero]

end integ
end SchurAux

namespace CharAux
open ParallelSU2.Reduction SymRepAux SchurAux QAlgorithms.Papers.Independent.Next46.P36

lemma weyl_rec (m : ℕ) (g : SU2) :
    weylCharacter 2 g * weylCharacter (m + 1) g = weylCharacter (m + 2) g + weylCharacter m g := by
  simp only [weylCharacter]
  rw [show ((m + 2 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 2 by push_cast; ring,
    show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 1 by push_cast; ring,
    show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num, Polynomial.Chebyshev.U_add_two,
    Polynomial.Chebyshev.U_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

lemma weyl_zero (g : SU2) : weylCharacter 0 g = 0 := by
  simp [weylCharacter]

variable [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
  (dg : Measure SU2) [IsProbabilityMeasure dg] [dg.IsMulLeftInvariant]

theorem weyl_orth (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ g, (weylCharacter a g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if a = b then 1 else 0 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have e : ∀ g, (weylCharacter (a' + 1) g : ℂ) * (weylCharacter (b' + 1) g : ℂ) =
      ((spinIrrep a').matrix g).trace * conj (((spinIrrep b').matrix g).trace) := by
    intro g; rw [spinIrrep_trace, spinIrrep_trace, Complex.conj_ofReal]
  simp_rw [e]
  split_ifs with hab
  · have : a' = b' := by omega
    subst this; exact char_orth_self dg _
  · exact char_orth_ne dg _ _ (by show a' + 1 ≠ b' + 1; omega)

end CharAux

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace ParallelSU2.Reduction.Aux
open ParallelSU2.Reduction QAlgorithms.Papers.Independent.Next46.P36 Matrix

/-- PSD with unit diagonal: off-diagonal entries have norm at most one (2x2 minor). -/
theorem entry_norm_le_one {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef)
    (hd : ∀ k, T k k = 1) (k l : Fin d) (hkl : k ≠ l) : ‖T k l‖ ≤ 1 := by
  have hH : T l k = conj (T k l) := by
    have := congrFun (congrFun hT.1 l) k
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; simp
  set t := T k l with ht
  set v : Fin d → ℂ := fun i => if i = k then -t else if i = l then 1 else 0 with hv
  have hmv : ∀ i, (T *ᵥ v) i = T i k * (-t) + T i l := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_eq_add k l hkl]
    · simp [v, hkl.symm]
    · intro j hj; simp [v, hj.1, hj.2]
  have hdot : star v ⬝ᵥ (T *ᵥ v) = ((1 - Complex.normSq t : ℝ) : ℂ) := by
    simp only [dotProduct, hmv]
    rw [Fintype.sum_eq_add k l hkl]
    · simp only [v, if_pos, if_neg hkl.symm, Pi.star_apply, hd, hH, ← ht]
      simp only [ite_true, star_neg, star_one]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [RCLike.star_def]
      ring
    · intro j hj; simp [v, hj.1, hj.2]
  have h := hT.dotProduct_mulVec_nonneg v
  rw [hdot, Complex.zero_le_real] at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg t]

theorem methodValue_le_hayashiError {d : ℕ} (x : Fin d → ℂ)
    (hx : ∑ k, Complex.normSq (x k) = 1)
    (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef) (hd : ∀ k, T k k = 1) :
    methodValue x ≤ hayashiError x T := by
  have key : ∀ k l : Fin d, (if k.val + 1 = l.val then
        (conj (x k) * x l * T k l + conj (x l) * x k * T l k).re else 0) ≤
      2 * (if k.val + 1 = l.val then ‖x k‖ * ‖x l‖ else 0) := by
    intro k l
    split_ifs with h
    · have hkl : k ≠ l := fun e => by rw [e] at h; omega
      have h1 := entry_norm_le_one T hT hd k l hkl
      have h2 := entry_norm_le_one T hT hd l k hkl.symm
      have b1 : (conj (x k) * x l * T k l).re ≤ ‖x k‖ * ‖x l‖ := by
        calc _ ≤ ‖conj (x k) * x l * T k l‖ := Complex.re_le_norm _
          _ = ‖x k‖ * ‖x l‖ * ‖T k l‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
          _ ≤ ‖x k‖ * ‖x l‖ := mul_le_of_le_one_right (by positivity) h1
      have b2 : (conj (x l) * x k * T l k).re ≤ ‖x k‖ * ‖x l‖ := by
        calc _ ≤ ‖conj (x l) * x k * T l k‖ := Complex.re_le_norm _
          _ = ‖x k‖ * ‖x l‖ * ‖T l k‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]; ring
          _ ≤ ‖x k‖ * ‖x l‖ := mul_le_of_le_one_right (by positivity) h2
      rw [Complex.add_re]; linarith
    · simp
  have hs : (∑ k : Fin d, ∑ l : Fin d, (if k.val + 1 = l.val then
        (conj (x k) * x l * T k l + conj (x l) * x k * T l k).re else 0)) ≤
      2 * ∑ k : Fin d, ∑ l : Fin d, (if k.val + 1 = l.val then ‖x k‖ * ‖x l‖ else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => key k l
  unfold methodValue hayashiError
  simp only [hd, Complex.one_re, mul_one, hx]
  linarith

theorem conj_mul_phase (z : ℂ) : conj z * coefficientPhase z = (‖z‖ : ℂ) := by
  unfold coefficientPhase
  split_ifs with h
  · simp [h]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [mul_div_assoc', Complex.conj_mul', div_eq_iff hn]; ring

theorem mul_conj_phase (z : ℂ) : z * conj (coefficientPhase z) = (‖z‖ : ℂ) := by
  have := congrArg conj (conj_mul_phase z)
  simpa [mul_comm] using this

theorem phase_mul_conj (z : ℂ) : coefficientPhase z * conj (coefficientPhase z) = 1 := by
  unfold coefficientPhase
  split_ifs with h
  · simp
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', div_eq_one_iff_eq
      (mul_ne_zero hn hn)]
    ring

theorem hayashiError_phaseAligned {d : ℕ} (x : Fin d → ℂ)
    (hx : ∑ k, Complex.normSq (x k) = 1) :
    hayashiError x (phaseAligned x) = methodValue x := by
  have e : ∀ k l : Fin d,
      (conj (x k) * x l * (coefficientPhase (x k) * conj (coefficientPhase (x l))) +
        conj (x l) * x k * (coefficientPhase (x l) * conj (coefficientPhase (x k)))).re =
      2 * (‖x k‖ * ‖x l‖) := by
    intro k l
    rw [show conj (x k) * x l * (coefficientPhase (x k) * conj (coefficientPhase (x l))) =
        (conj (x k) * coefficientPhase (x k)) * (x l * conj (coefficientPhase (x l))) by ring,
      show conj (x l) * x k * (coefficientPhase (x l) * conj (coefficientPhase (x k))) =
        (conj (x l) * coefficientPhase (x l)) * (x k * conj (coefficientPhase (x k))) by ring,
      conj_mul_phase, mul_conj_phase, conj_mul_phase, mul_conj_phase]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e2 : ∀ k l : Fin d, (if k.val + 1 = l.val then 2 * (‖x k‖ * ‖x l‖) else (0 : ℝ)) =
      2 * (if k.val + 1 = l.val then ‖x k‖ * ‖x l‖ else 0) := by
    intro k l; split_ifs <;> simp
  unfold hayashiError methodValue phaseAligned
  simp only [Matrix.of_apply, phase_mul_conj, Complex.one_re, mul_one, hx, e, e2,
    ← Finset.mul_sum]
  ring

theorem scaled_limit :
    Tendsto (fun d : ℕ => (2 * (d : ℝ) - 1) ^ 2 * Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2)
      atTop (𝓝 (Real.pi ^ 2)) := by
  have hden : Tendsto (fun d : ℕ => 2 * (d : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun d : ℕ => Real.pi / (2 * (d : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h2 : Tendsto (fun d : ℕ => 1 - 3 / (2 * (d : ℝ) + 2)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden :
      Tendsto (fun d : ℕ => (3 : ℝ) / (2 * (d : ℝ) + 2)) atTop (𝓝 0))
  have h3 : Tendsto (fun d : ℕ => Real.sinc (Real.pi / (2 * (d : ℝ) + 2))) atTop (𝓝 1) := by
    have := (Real.continuous_sinc.tendsto 0).comp h1
    rw [Real.sinc_zero] at this
    exact this
  have h4 := ((tendsto_const_nhds (x := Real.pi)).mul (h2.mul h3)).pow 2
  simp only [mul_one] at h4
  refine h4.congr fun d => ?_
  have hpos : (0 : ℝ) < 2 * (d : ℝ) + 2 := by positivity
  have hy : Real.pi / (2 * (d : ℝ) + 2) ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hy]
  field_simp
  ring

/-- Zero-extension of a `Fin d` vector to `ℕ`. -/
noncomputable def ext0 {d : ℕ} (f : Fin d → ℝ) (i : ℕ) : ℝ := if h : i < d then f ⟨i, h⟩ else 0

theorem ext0_at_d {d : ℕ} (f : Fin d → ℝ) : ext0 f d = 0 := by simp [ext0]

theorem adj_sum_eq {d : ℕ} (f : Fin d → ℝ) :
    (∑ k : Fin d, ∑ l : Fin d, if k.val + 1 = l.val then f k * f l else 0) =
      ∑ i ∈ Finset.range d, ext0 f i * ext0 f (i + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 f i * ext0 f (i + 1))]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k.val + 1 < d
  · rw [Finset.sum_eq_single ⟨k.val + 1, h⟩]
    · simp [ext0, h, k.isLt]
    · intro l _ hl
      rw [if_neg]
      intro e; apply hl; exact Fin.ext (by simp [← e])
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [ext0, h]
    · intro l _
      rw [if_neg]
      intro e; have := l.isLt; omega

theorem sq_sum_eq {d : ℕ} (f : Fin d → ℝ) :
    ∑ k : Fin d, f k ^ 2 = ∑ i ∈ Finset.range d, ext0 f i ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 f i ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ext0, k.isLt]

/-- The path-graph eigen-identity behind Hayashi's `cos(π/(d+1))`. -/
theorem sos_identity (d : ℕ) (a : ℕ → ℝ) (ha : a d = 0) :
    ∑ i ∈ Finset.range d,
      (a i ^ 2 * (Real.sin (((i : ℝ) + 2) * (Real.pi / (d + 1))) /
          Real.sin (((i : ℝ) + 1) * (Real.pi / (d + 1)))) +
        a (i + 1) ^ 2 * (Real.sin (((i : ℝ) + 1) * (Real.pi / (d + 1))) /
          Real.sin (((i : ℝ) + 2) * (Real.pi / (d + 1))))) =
      2 * Real.cos (Real.pi / (d + 1)) * ∑ i ∈ Finset.range d, a i ^ 2 := by
  set θ := Real.pi / (d + 1) with hθ
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have spos : ∀ i : ℕ, i < d → 0 < Real.sin (((i : ℝ) + 1) * θ) := by
    intro i hi
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]; positivity
    · rw [hθ, mul_div_assoc', div_lt_iff₀ hdpos]
      have : (i : ℝ) + 1 < d + 1 := by exact_mod_cast Nat.succ_lt_succ hi
      nlinarith [Real.pi_pos]
  set g : ℕ → ℝ := fun j => a j ^ 2 * (Real.sin ((j : ℝ) * θ) / Real.sin (((j : ℝ) + 1) * θ))
    with hg
  have hshift : ∑ i ∈ Finset.range d, a (i + 1) ^ 2 * (Real.sin (((i : ℝ) + 1) * θ) /
        Real.sin (((i : ℝ) + 2) * θ)) = ∑ i ∈ Finset.range d, g i := by
    have h1 := Finset.sum_range_succ' g d
    have h2 := Finset.sum_range_succ g d
    have hg0 : g 0 = 0 := by simp [hg]
    have hgd : g d = 0 := by simp [hg, ha]
    have e : ∀ i ∈ Finset.range d, a (i + 1) ^ 2 * (Real.sin (((i : ℝ) + 1) * θ) /
        Real.sin (((i : ℝ) + 2) * θ)) = g (i + 1) := by
      intro i _; simp only [hg]; push_cast; ring_nf
    rw [Finset.sum_congr rfl e]
    linarith
  rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hw := spos i (Finset.mem_range.mp hi)
  have trig : Real.sin (((i : ℝ) + 2) * θ) + Real.sin ((i : ℝ) * θ) =
      2 * Real.cos θ * Real.sin (((i : ℝ) + 1) * θ) := by
    have e1 : ((i : ℝ) + 2) * θ = ((i : ℝ) + 1) * θ + θ := by ring
    have e2 : (i : ℝ) * θ = ((i : ℝ) + 1) * θ - θ := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]; ring
  simp only [hg]
  rw [← mul_add, ← add_div, trig]
  field_simp

theorem path_le (d : ℕ) (a : ℕ → ℝ) (ha : a d = 0) :
    ∑ i ∈ Finset.range d, a i * a (i + 1) ≤
      Real.cos (Real.pi / (d + 1)) * ∑ i ∈ Finset.range d, a i ^ 2 := by
  have hid := sos_identity d a ha
  set θ := Real.pi / (d + 1) with hθ
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have spos : ∀ i : ℕ, i < d → 0 < Real.sin (((i : ℝ) + 1) * θ) := by
    intro i hi
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]; positivity
    · rw [hθ, mul_div_assoc', div_lt_iff₀ hdpos]
      have : (i : ℝ) + 1 < d + 1 := by exact_mod_cast Nat.succ_lt_succ hi
      nlinarith [Real.pi_pos]
  have key : ∀ i ∈ Finset.range d, 2 * (a i * a (i + 1)) ≤
      a i ^ 2 * (Real.sin (((i : ℝ) + 2) * θ) / Real.sin (((i : ℝ) + 1) * θ)) +
        a (i + 1) ^ 2 * (Real.sin (((i : ℝ) + 1) * θ) / Real.sin (((i : ℝ) + 2) * θ)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hw := spos i hi'
    by_cases h : i + 1 < d
    · have hu := spos (i + 1) h
      push_cast at hu
      rw [show ((i : ℝ) + 1 + 1) = (i : ℝ) + 2 by ring] at hu
      set u := Real.sin (((i : ℝ) + 2) * θ)
      set w := Real.sin (((i : ℝ) + 1) * θ)
      have : a i ^ 2 * (u / w) + a (i + 1) ^ 2 * (w / u) - 2 * (a i * a (i + 1)) =
          (a i * u - a (i + 1) * w) ^ 2 / (u * w) := by
        field_simp; ring
      have : 0 ≤ (a i * u - a (i + 1) * w) ^ 2 / (u * w) := by positivity
      linarith
    · have hd : i + 1 = d := by omega
      have hu : Real.sin (((i : ℝ) + 2) * θ) = 0 := by
        have : ((i : ℝ) + 2) * θ = Real.pi := by
          rw [hθ]; field_simp
          have : (d : ℝ) = i + 1 := by exact_mod_cast hd.symm
          rw [this]; ring
        rw [this, Real.sin_pi]
      rw [hd, ha, hu]; simp
  have := Finset.sum_le_sum key
  rw [hid, ← Finset.mul_sum] at this
  linarith

theorem path_eq (d : ℕ) :
    ∑ i ∈ Finset.range d, Real.sin (((i : ℝ) + 1) * (Real.pi / (d + 1))) *
        Real.sin ((((i + 1 : ℕ) : ℝ) + 1) * (Real.pi / (d + 1))) =
      Real.cos (Real.pi / (d + 1)) *
        ∑ i ∈ Finset.range d, Real.sin (((i : ℝ) + 1) * (Real.pi / (d + 1))) ^ 2 := by
  set θ := Real.pi / (d + 1) with hθ
  set a : ℕ → ℝ := fun i => Real.sin (((i : ℝ) + 1) * θ) with ha
  have had : a d = 0 := by
    simp only [ha]
    have : ((d : ℝ) + 1) * θ = Real.pi := by rw [hθ]; field_simp
    rw [this, Real.sin_pi]
  have hid := sos_identity d a had
  have e : ∀ i ∈ Finset.range d,
      a i ^ 2 * (Real.sin (((i : ℝ) + 2) * θ) / Real.sin (((i : ℝ) + 1) * θ)) +
        a (i + 1) ^ 2 * (Real.sin (((i : ℝ) + 1) * θ) / Real.sin (((i : ℝ) + 2) * θ)) =
      2 * (a i * a (i + 1)) := by
    intro i _
    have h2 : a (i + 1) = Real.sin (((i : ℝ) + 2) * θ) := by
      simp only [ha]; push_cast; ring_nf
    rw [h2]
    simp only [ha]
    by_cases hw : Real.sin (((i : ℝ) + 1) * θ) = 0
    · rw [hw]; simp
    by_cases hu : Real.sin (((i : ℝ) + 2) * θ) = 0
    · rw [hu]; simp
    field_simp; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum] at hid
  have : ∑ i ∈ Finset.range d, a i * a (i + 1) = Real.cos θ * ∑ i ∈ Finset.range d, a i ^ 2 := by
    linarith
  simpa [ha] using this

theorem sin_pos_path (d i : ℕ) (hi : i < d) :
    0 < Real.sin (((i : ℝ) + 1) * (Real.pi / (d + 1))) := by
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · rw [mul_div_assoc', div_lt_iff₀ hdpos]
    have : (i : ℝ) + 1 < d + 1 := by exact_mod_cast Nat.succ_lt_succ hi
    nlinarith [Real.pi_pos]

/-- Conjunct (3): the least value of Hayashi's `v(x)` is `sin²(π/(2d+2))`. -/
theorem methodValue_isLeast (d : ℕ) (hd : 1 ≤ d) :
    IsLeast {r : ℝ | ∃ x : Fin d → ℂ, ∑ k, Complex.normSq (x k) = 1 ∧ r = methodValue x}
      (Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2) := by
  set θ := Real.pi / ((d : ℝ) + 1) with hθ
  have hsin : Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2 = 1 / 2 - Real.cos θ / 2 := by
    have : θ = 2 * (Real.pi / (2 * (d : ℝ) + 2)) := by rw [hθ]; field_simp; try ring
    rw [this, Real.cos_two_mul, Real.cos_sq']
    ring
  have mv : ∀ x : Fin d → ℂ, methodValue x = 1 / 2 * (1 - ∑ i ∈ Finset.range d,
      ext0 (fun k => ‖x k‖) i * ext0 (fun k => ‖x k‖) (i + 1)) := by
    intro x; unfold methodValue; rw [← adj_sum_eq (fun k => ‖x k‖)]
  constructor
  · set S := ∑ i ∈ Finset.range d, Real.sin (((i : ℝ) + 1) * θ) ^ 2 with hSdef
    have hS : 0 < S := by
      have h0 : 0 < Real.sin ((((0 : ℕ) : ℝ) + 1) * θ) := by
        rw [hθ]; exact sin_pos_path d 0 (by omega)
      have := Finset.single_le_sum (f := fun i : ℕ => Real.sin (((i : ℝ) + 1) * θ) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (show 0 < d by omega))
      simp only [Nat.cast_zero] at this h0
      rw [← hSdef] at this
      nlinarith [sq_pos_of_pos h0]
    have hsq : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    set b : ℕ → ℝ := fun i => Real.sin (((i : ℝ) + 1) * θ) / Real.sqrt S with hb
    set x : Fin d → ℂ := fun k => ((b k.val : ℝ) : ℂ) with hx
    have hbpos : ∀ i, i < d → 0 < b i := fun i hi => div_pos (sin_pos_path d i hi) hsq
    have hext : ∀ i, i ≤ d → ext0 (fun k => ‖x k‖) i = b i := by
      intro i hi
      rcases lt_or_eq_of_le hi with h | h
      · simp only [ext0, h, dif_pos, hx, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (hbpos i h)
      · subst h
        rw [ext0_at_d]
        simp only [hb]
        have : ((i : ℝ) + 1) * θ = Real.pi := by rw [hθ]; field_simp
        rw [this, Real.sin_pi, zero_div]
    refine ⟨x, ?_, ?_⟩
    · have e : ∀ k : Fin d, Complex.normSq (x k) = ext0 (fun k => ‖x k‖) k.val ^ 2 := by
        intro k; rw [hext k.val k.isLt.le]; simp [hx, Complex.normSq_ofReal, sq]
      rw [Finset.sum_congr rfl fun k _ => e k,
        Fin.sum_univ_eq_sum_range (fun i => ext0 (fun k => ‖x k‖) i ^ 2) d]
      rw [Finset.sum_congr rfl fun i hi => by rw [hext i (Finset.mem_range.mp hi).le]]
      simp only [hb, div_pow, Real.sq_sqrt hS.le, ← Finset.sum_div, ← hSdef]
      exact div_self hS.ne'
    · rw [mv, hsin]
      rw [Finset.sum_congr rfl fun i hi => by
        rw [hext i (Finset.mem_range.mp hi).le, hext (i + 1) (Finset.mem_range.mp hi)]]
      have hp := path_eq d
      rw [← hθ, ← hSdef] at hp
      have : ∑ i ∈ Finset.range d, b i * b (i + 1) = Real.cos θ := by
        simp only [hb]
        rw [Finset.sum_congr rfl fun i _ => by
          rw [div_mul_div_comm, ← sq, Real.sq_sqrt hS.le]]
        rw [← Finset.sum_div, hp, mul_div_assoc, div_self hS.ne', mul_one]
      rw [this]; ring
  · rintro r ⟨x, hx, rfl⟩
    rw [mv, hsin]
    have h1 := path_le d (ext0 (fun k => ‖x k‖)) (ext0_at_d _)
    have h2 : ∑ i ∈ Finset.range d, ext0 (fun k => ‖x k‖) i ^ 2 = 1 := by
      rw [← sq_sum_eq (fun k => ‖x k‖), ← hx]
      exact Finset.sum_congr rfl fun k _ => (Complex.normSq_eq_norm_sq (x k)).symm
    rw [h2, mul_one] at h1
    rw [← hθ] at h1
    linarith

end ParallelSU2.Reduction.Aux

set_option autoImplicit false
open scoped BigOperators ComplexConjugate Matrix ComplexOrder

namespace C2Aux
open ParallelSU2.Reduction QAlgorithms.Papers.Independent.Next46.P36 Matrix

section alg
variable {d : ℕ} (D : Fin d → BasedIrrep SU2)

def vecOf (A : ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) : CanonicalIndex D → ℂ :=
  fun p => A p.1 p.2.1 p.2.2

lemma act_vecOf (h : SU2) (A : ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) :
    canonicalAction D h *ᵥ vecOf D A = vecOf D (fun s => (D s).matrix h * A s) := by
  ext ⟨s, a, b⟩
  simp only [Matrix.mulVec, dotProduct, vecOf, canonicalAction, Fintype.sum_sigma]
  rw [Finset.sum_eq_single s (fun s' _ hs' => by
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hs')]) (by simp)]
  simp [Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.mul_apply, Fintype.sum_prod_type]

lemma dot_vecOf (A B : ∀ s, Matrix (Fin (D s).dim) (Fin (D s).dim) ℂ) :
    star (vecOf D A) ⬝ᵥ vecOf D B = ∑ s, ∑ a, ∑ b, conj (A s a b) * B s a b := by
  simp [dotProduct, vecOf, Fintype.sum_sigma, Fintype.sum_prod_type]

lemma bell_eq (k : Fin d) :
    (fun p => blockBellVector D k p) =
      vecOf D (fun s => (Real.sqrt (D s).dim : ℂ) • (if s = k then 1 else 0)) := by
  funext p
  simp [blockBellVector, componentVector, vecOf]

lemma input_eq (x : Fin d → ℂ) :
    (fun p => canonicalInput D x (fun _ => 1) p) =
      vecOf D (fun s => (x s / (Real.sqrt (D s).dim : ℂ)) • 1) := by
  funext p
  simp [canonicalInput, vecOf, Matrix.one_apply]

lemma seed_eq (T : Matrix (Fin d) (Fin d) ℂ) :
    hayashiSeed D T = ∑ k, ∑ l, T k l •
      vecMulVec (fun p => blockBellVector D k p) (star (fun p => blockBellVector D l p)) := by
  simp only [hayashiSeed]
  rfl

lemma conj_vmv {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    A * vecMulVec u (star v) * Aᴴ = vecMulVec (A *ᵥ u) (star (A *ᵥ v)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

lemma conj_sum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (T : Matrix (Fin d) (Fin d) ℂ)
    (u : Fin d → ι → ℂ) :
    QAlgorithms.conjSuperop A (∑ k, ∑ l, T k l • vecMulVec (u k) (star (u l))) =
      ∑ k, ∑ l, T k l • vecMulVec (A *ᵥ u k) (star (A *ᵥ u l)) := by
  simp only [QAlgorithms.conjSuperop, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, conj_vmv]

/-- the rotated Bell vector `U(h) b_k`, entrywise. -/
lemma w_apply (h : SU2) (k : Fin d) (p : CanonicalIndex D) :
    (canonicalAction D h *ᵥ fun q => blockBellVector D k q) p =
      if p.1 = k then (Real.sqrt (D p.1).dim : ℂ) * (D p.1).matrix h p.2.1 p.2.2 else 0 := by
  rw [bell_eq, act_vecOf]
  simp only [vecOf]
  split_ifs with hk
  · simp [hk, Matrix.mul_smul]
  · simp [hk]

lemma seed_psd (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef) :
    (hayashiSeed D T).PosSemidef := by
  have e : hayashiSeed D T =
      (Matrix.of fun p k => blockBellVector D k p) * T * (Matrix.of fun p k => blockBellVector D k p)ᴴ := by
    ext p q
    simp only [hayashiSeed, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]; exact hT.mul_mul_conjTranspose_same _

lemma F_apply (T : Matrix (Fin d) (Fin d) ℂ) (h : SU2) (p q : CanonicalIndex D) :
    QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T) p q =
      T p.1 q.1 * ((Real.sqrt (D p.1).dim : ℂ) * (Real.sqrt (D q.1).dim : ℂ)) *
        ((D p.1).matrix h p.2.1 p.2.2 * conj ((D q.1).matrix h q.2.1 q.2.2)) := by
  rw [seed_eq, conj_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, w_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single p.1 (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  rw [Finset.sum_eq_single q.1 (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp only [if_true, star_mul', RCLike.star_def, Complex.conj_ofReal]
  ring

lemma F_cont (T : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun h => QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T)) := by
  refine continuous_matrix fun p q => ?_
  simp_rw [F_apply]
  exact continuous_const.mul (((D p.1).continuous.matrix_elem _ _).mul
    (Complex.continuous_conj.comp ((D q.1).continuous.matrix_elem _ _)))

end alg

section anal
open MeasureTheory
variable {d : ℕ} (D : Fin d → BasedIrrep SU2)
  [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
  (dg : Measure SU2) [IsProbabilityMeasure dg]

lemma int_F_entry (T : Matrix (Fin d) (Fin d) ℂ) (hT1 : ∀ k, T k k = 1)
    (hne : ∀ s s', s ≠ s' → ∀ i i' m m',
      ∫ h, (D s).matrix h i i' * conj ((D s').matrix h m m') ∂dg = 0)
    (heq : ∀ s i i' m m', ∫ h, (D s).matrix h i i' * conj ((D s).matrix h m m') ∂dg =
      if i = m ∧ i' = m' then 1 / ((D s).dim : ℂ) else 0)
    (p q : CanonicalIndex D) :
    ∫ h, QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T) p q ∂dg =
      (1 : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) p q := by
  simp_rw [F_apply]
  rw [integral_const_mul]
  obtain ⟨s, a, b⟩ := p
  obtain ⟨s', a', b'⟩ := q
  by_cases hs : s = s'
  · subst hs
    have hn : ((D s).dim : ℂ) ≠ 0 := by exact_mod_cast (D s).positive.ne'
    have hsq : (Real.sqrt (D s).dim : ℂ) * (Real.sqrt (D s).dim : ℂ) = (D s).dim := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
    simp only
    rw [heq, hT1, hsq]
    simp only [Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and]
    split_ifs <;> simp [hn]
  · simp only
    rw [hne s s' hs]
    simp [Matrix.one_apply, hs]

section povm
open scoped Matrix.Norms.L2Operator

lemma integrable_F (T : Matrix (Fin d) (Fin d) ℂ) :
    Integrable (fun h => QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T)) dg :=
  (F_cont D T).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

noncomputable def entryCLM {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) :
    Matrix ι ι ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A p q, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma integral_F (T : Matrix (Fin d) (Fin d) ℂ) (hT1 : ∀ k, T k k = 1)
    (hne : ∀ s s', s ≠ s' → ∀ i i' m m',
      ∫ h, (D s).matrix h i i' * conj ((D s').matrix h m m') ∂dg = 0)
    (heq : ∀ s i i' m m', ∫ h, (D s).matrix h i i' * conj ((D s).matrix h m m') ∂dg =
      if i = m ∧ i' = m' then 1 / ((D s).dim : ℂ) else 0) :
    ∫ h, QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T) ∂dg = 1 := by
  ext p q
  have hc := (entryCLM p q).integral_comp_comm (integrable_F D dg T)
  rw [show (∫ h, QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T) ∂dg) p q =
    entryCLM p q (∫ h, QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T) ∂dg)
    from rfl, ← hc]
  exact int_F_entry D dg T hT1 hne heq p q

lemma measurable_F (T : Matrix (Fin d) (Fin d) ℂ) :
    @Measurable SU2 _ _ (QAlgorithms.Measurements.matrixMeasurable (CanonicalIndex D))
      (fun h => QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T)) := by
  letI : MeasurableSpace (Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) := borel _
  haveI : BorelSpace (Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) := ⟨rfl⟩
  exact (F_cont D T).measurable

end povm
end anal

section risk
open MeasureTheory
variable {d : ℕ} (D : Fin d → BasedIrrep SU2)

lemma rep_inv (B : BasedIrrep SU2) (g : SU2) : B.matrix g⁻¹ = (B.matrix g)ᴴ := by
  have h1 : B.matrix g⁻¹ * B.matrix g = 1 := by rw [← B.mul, inv_mul_cancel, B.one]
  have h2 := (B.unitary g).2
  calc B.matrix g⁻¹ = B.matrix g⁻¹ * (B.matrix g * (B.matrix g)ᴴ) := by rw [h2, Matrix.mul_one]
    _ = (B.matrix g)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma inner_w_phi (hD : IsSpinFamily D) (x : Fin d → ℂ) (h g : SU2) (l : Fin d) :
    star (canonicalAction D h *ᵥ fun q => blockBellVector D l q) ⬝ᵥ
      (canonicalAction D g *ᵥ fun q => canonicalInput D x (fun _ => 1) q) =
      x l * (weylCharacter (2 * (l.val + 1)) (g⁻¹ * h) : ℂ) := by
  have hn : (Real.sqrt (D l).dim : ℂ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt (D l).dim := Real.sqrt_pos.mpr (by exact_mod_cast (D l).positive)
    exact_mod_cast this.ne'
  have htr : ((weylCharacter (2 * (l.val + 1)) (g⁻¹ * h) : ℝ) : ℂ) =
      ∑ a, ∑ b, conj ((D l).matrix h a b) * (D l).matrix g a b := by
    rw [← Complex.conj_ofReal, ← (hD l).2, (D l).mul, rep_inv]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      RCLike.star_def, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [bell_eq, input_eq, act_vecOf, act_vecOf, dot_vecOf,
    Finset.sum_eq_single l (fun s _ hs => by simp [hs]) (by simp), htr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [if_true, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, map_mul,
    Complex.conj_ofReal]
  field_simp

lemma eff_eq (hD : IsSpinFamily D) (x : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) (h g : SU2) :
    QAlgorithms.effectProb (QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T))
      (QAlgorithms.conjSuperop (canonicalAction D g)
        (QAlgorithms.pureDensity (canonicalInput D x (fun _ => 1)))) =
    (∑ k, ∑ l, T k l * conj (x k) * x l *
      ((weylCharacter (2 * (k.val + 1)) (g⁻¹ * h) * weylCharacter (2 * (l.val + 1)) (g⁻¹ * h) : ℝ) : ℂ)).re := by
  have hp : QAlgorithms.pureDensity (canonicalInput D x (fun _ => 1)) =
      vecMulVec (fun p => canonicalInput D x (fun _ => 1) p)
        (star (fun p => canonicalInput D x (fun _ => 1) p)) := rfl
  have hc : ∀ (A : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ) (u : CanonicalIndex D → ℂ),
      QAlgorithms.conjSuperop A (vecMulVec u (star u)) = vecMulVec (A *ᵥ u) (star (A *ᵥ u)) :=
    fun A u => conj_vmv A u u
  have e1 : ∀ l : Fin d, (canonicalAction D g *ᵥ fun q => canonicalInput D x (fun _ => 1) q) ⬝ᵥ
      star (canonicalAction D h *ᵥ fun q => blockBellVector D l q) =
      x l * (weylCharacter (2 * (l.val + 1)) (g⁻¹ * h) : ℂ) := by
    intro l; rw [dotProduct_comm]; exact inner_w_phi D hD x h g l
  have e2 : ∀ k : Fin d, (canonicalAction D h *ᵥ fun q => blockBellVector D k q) ⬝ᵥ
      star (canonicalAction D g *ᵥ fun q => canonicalInput D x (fun _ => 1) q) =
      conj (x k) * (weylCharacter (2 * (k.val + 1)) (g⁻¹ * h) : ℂ) := by
    intro k; rw [dotProduct_star, e1]
    simp only [star_mul', RCLike.star_def, Complex.conj_ofReal]
  rw [seed_eq, conj_sum, hp, hc]
  simp only [QAlgorithms.effectProb, Matrix.sum_mul, Matrix.smul_mul, vecMulVec_mul_vecMulVec,
    Matrix.trace_sum, Matrix.trace_smul, trace_vecMulVec]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [inner_w_phi D hD x h g l, dotProduct_smul, e2]
  simp only [smul_eq_mul]
  push_cast
  ring

lemma cost_eq (htr : ∀ m : SU2, ((((m : Matrix (Fin 2) (Fin 2) ℂ).trace.re : ℝ) : ℂ) =
      (m : Matrix (Fin 2) (Fin 2) ℂ).trace)) (h g : SU2) :
    bellCost h g = 1 - weylCharacter 2 (g⁻¹ * h) ^ 2 / 4 := by
  have e : ((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (h : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((g⁻¹ * h : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  unfold bellCost weylCharacter
  rw [e, ← htr, Complex.normSq_ofReal, show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num,
    Polynomial.Chebyshev.U_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat, Complex.ofReal_re]
  ring

lemma weyl_cont (j : ℕ) : Continuous (fun g : SU2 => weylCharacter j g) := by
  unfold weylCharacter
  exact (Polynomial.continuous _).comp
    ((Complex.continuous_re.comp (continuous_subtype_val.matrix_trace)).div_const 2)

lemma weyl_rec (m : ℕ) (g : SU2) :
    weylCharacter 2 g * weylCharacter (m + 1) g = weylCharacter (m + 2) g + weylCharacter m g := by
  simp only [weylCharacter]
  rw [show ((m + 2 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 2 by push_cast; ring,
    show ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℤ) - 1) + 1 by push_cast; ring,
    show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num, Polynomial.Chebyshev.U_add_two,
    Polynomial.Chebyshev.U_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

lemma weyl_zero (g : SU2) : weylCharacter 0 g = 0 := by
  simp [weylCharacter]

variable [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
  (dg : Measure SU2) [IsProbabilityMeasure dg]

lemma integ (f : SU2 → ℂ) (hf : Continuous f) : Integrable f dg :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

lemma cw (j : ℕ) : Continuous (fun g : SU2 => (weylCharacter j g : ℂ)) :=
  Complex.continuous_ofReal.comp (weyl_cont j)

lemma weyl_orth' (hW : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ g, (weylCharacter a g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if a = b then 1 else 0)
    (c b : ℕ) (hb : 1 ≤ b) :
    ∫ g, (weylCharacter c g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if c = b then 1 else 0 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp only [weyl_zero, Complex.ofReal_zero, zero_mul, integral_zero]
    rw [if_neg (by omega)]
  · exact hW c b hc hb

lemma I_eq (hW : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ g, (weylCharacter a g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if a = b then 1 else 0)
    (k l : ℕ) :
    ∫ m, ((weylCharacter (2 * (k + 1)) m * weylCharacter (2 * (l + 1)) m *
      (1 - weylCharacter 2 m ^ 2 / 4) : ℝ) : ℂ) ∂dg =
      (if k = l then 1 / 2 else 0) -
        ((if k + 1 = l then 1 else 0) + (if l + 1 = k then 1 else 0)) / 4 := by
  have pt : ∀ m : SU2, ((weylCharacter (2 * (k + 1)) m * weylCharacter (2 * (l + 1)) m *
      (1 - weylCharacter 2 m ^ 2 / 4) : ℝ) : ℂ) =
      (weylCharacter (2 * (k + 1)) m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / 2 -
      (weylCharacter (2 * k + 4) m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / 4 -
      (weylCharacter (2 * k) m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / 4 := by
    intro m
    have r1 : weylCharacter 2 m * weylCharacter (2 * (k + 1)) m =
        weylCharacter (2 * k + 3) m + weylCharacter (2 * k + 1) m := by
      have := weyl_rec (2 * k + 1) m
      rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, show 2 * k + 1 + 2 = 2 * k + 3 by ring] at this
    have r2 : weylCharacter 2 m * weylCharacter (2 * k + 3) m =
        weylCharacter (2 * k + 4) m + weylCharacter (2 * (k + 1)) m := by
      have := weyl_rec (2 * k + 2) m
      rwa [show 2 * k + 2 + 1 = 2 * k + 3 by ring, show 2 * k + 2 + 2 = 2 * k + 4 by ring,
        show 2 * k + 2 = 2 * (k + 1) by ring] at this
    have r3 : weylCharacter 2 m * weylCharacter (2 * k + 1) m =
        weylCharacter (2 * (k + 1)) m + weylCharacter (2 * k) m := by
      have := weyl_rec (2 * k) m
      rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at this
    have key : weylCharacter (2 * (k + 1)) m * weylCharacter (2 * (l + 1)) m *
        (1 - weylCharacter 2 m ^ 2 / 4) =
        weylCharacter (2 * (k + 1)) m * weylCharacter (2 * (l + 1)) m / 2 -
        weylCharacter (2 * k + 4) m * weylCharacter (2 * (l + 1)) m / 4 -
        weylCharacter (2 * k) m * weylCharacter (2 * (l + 1)) m / 4 := by
      linear_combination (-(weylCharacter (2 * (l + 1)) m / 4)) *
        (weylCharacter 2 m * r1 + r2 + r3)
    rw [key]; push_cast; ring
  simp_rw [pt]
  have hI : ∀ (c : ℕ) (r : ℂ), Integrable (fun m : SU2 =>
      (weylCharacter c m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / r) dg :=
    fun c r => integ dg _ (((cw c).mul (cw _)).div_const r)
  have j1 : Integrable (fun m : SU2 =>
      (weylCharacter (2 * (k + 1)) m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / 2 -
      (weylCharacter (2 * k + 4) m : ℂ) * (weylCharacter (2 * (l + 1)) m : ℂ) / 4) dg :=
    (hI _ 2).sub (hI _ 4)
  rw [integral_sub j1 (hI _ 4), integral_sub (hI _ 2) (hI _ 4), integral_div, integral_div,
    integral_div,
    weyl_orth' dg hW _ _ (by omega), weyl_orth' dg hW _ _ (by omega),
    weyl_orth' dg hW _ _ (by omega)]
  simp only [show (2 * (k + 1) = 2 * (l + 1)) ↔ k = l by omega,
    show (2 * k + 4 = 2 * (l + 1)) ↔ k + 1 = l by omega,
    show (2 * k = 2 * (l + 1)) ↔ l + 1 = k by omega]
  split_ifs <;> ring

lemma alg_eq (x : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) :
    (∑ k : Fin d, ∑ l : Fin d, T k l * conj (x k) * x l *
      ((if k.val = l.val then 1 / 2 else 0) -
        ((if k.val + 1 = l.val then 1 else 0) + (if l.val + 1 = k.val then 1 else 0)) / 4 : ℂ)).re =
      hayashiError x T := by
  have hI : ∀ k l : Fin d, T k l * conj (x k) * x l *
      ((if k.val = l.val then 1 / 2 else 0) -
        ((if k.val + 1 = l.val then 1 else 0) + (if l.val + 1 = k.val then 1 else 0)) / 4 : ℂ) =
      ((1 / 2 : ℝ) : ℂ) * (if k.val = l.val then T k l * conj (x k) * x l else 0) -
      ((1 / 4 : ℝ) : ℂ) * (if k.val + 1 = l.val then T k l * conj (x k) * x l else 0) -
      ((1 / 4 : ℝ) : ℂ) * (if l.val + 1 = k.val then T k l * conj (x k) * x l else 0) := by
    intro k l; split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hI k l]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have s1 : ∑ k : Fin d, ∑ l : Fin d, (if k.val = l.val then T k l * conj (x k) * x l else 0) =
      ∑ k, T k k * conj (x k) * x k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k (fun l _ hl => if_neg (fun h => hl (Fin.ext h).symm)) (by simp)]
    simp
  have s2 : ∑ k : Fin d, ∑ l : Fin d,
      (if l.val + 1 = k.val then T k l * conj (x k) * x l else 0) =
      ∑ k : Fin d, ∑ l : Fin d, (if k.val + 1 = l.val then T l k * conj (x l) * x k else 0) :=
    Finset.sum_comm
  rw [s1, s2]
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum]
  have a1 : ∀ k, (T k k * conj (x k) * x k).re = Complex.normSq (x k) * (T k k).re := by
    intro k
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.re_mul_ofReal]; ring
  have a2 : ∀ k l : Fin d, (if k.val + 1 = l.val then T k l * conj (x k) * x l else 0).re +
      (if k.val + 1 = l.val then T l k * conj (x l) * x k else 0).re =
      (if k.val + 1 = l.val then (conj (x k) * x l * T k l + conj (x l) * x k * T l k).re
        else 0) := by
    intro k l
    split_ifs
    · rw [Complex.add_re, show T k l * conj (x k) * x l = conj (x k) * x l * T k l by ring,
        show T l k * conj (x l) * x k = conj (x l) * x k * T l k by ring]
    · simp
  have hsum : (∑ k : Fin d, ∑ l : Fin d,
      (if k.val + 1 = l.val then T k l * conj (x k) * x l else 0).re) +
      (∑ k : Fin d, ∑ l : Fin d, (if k.val + 1 = l.val then T l k * conj (x l) * x k else 0).re) =
      ∑ k : Fin d, ∑ l : Fin d,
        (if k.val + 1 = l.val then (conj (x k) * x l * T k l + conj (x l) * x k * T l k).re
          else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => a2 k l
  simp only [a1]
  unfold hayashiError
  rw [← hsum]
  ring

lemma risk_eq [dg.IsMulLeftInvariant] (hD : IsSpinFamily D)
    (htr : ∀ m : SU2, ((((m : Matrix (Fin 2) (Fin 2) ℂ).trace.re : ℝ) : ℂ) =
      (m : Matrix (Fin 2) (Fin 2) ℂ).trace))
    (hW : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ g, (weylCharacter a g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if a = b then 1 else 0)
    (x : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) (g : SU2) :
    ∫ h, bellCost h g * QAlgorithms.effectProb
        (QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T))
        (QAlgorithms.conjSuperop (canonicalAction D g)
          (QAlgorithms.pureDensity (canonicalInput D x (fun _ => 1)))) ∂dg =
      hayashiError x T := by
  have hc2 : ∀ k l : Fin d, Continuous fun m : SU2 =>
      ((weylCharacter (2 * (k.val + 1)) m * weylCharacter (2 * (l.val + 1)) m *
        (1 - weylCharacter 2 m ^ 2 / 4) : ℝ) : ℂ) := fun k l =>
    Complex.continuous_ofReal.comp (((weyl_cont _).mul (weyl_cont _)).mul
      (continuous_const.sub (((weyl_cont 2).pow 2).div_const 4)))
  let ΦC : SU2 → ℂ := fun m => ∑ k : Fin d, ∑ l : Fin d, T k l * conj (x k) * x l *
    ((weylCharacter (2 * (k.val + 1)) m * weylCharacter (2 * (l.val + 1)) m *
      (1 - weylCharacter 2 m ^ 2 / 4) : ℝ) : ℂ)
  have hcont : Continuous ΦC := continuous_finset_sum _ fun k _ =>
    continuous_finset_sum _ fun l _ => continuous_const.mul (hc2 k l)
  have hpt : ∀ h, bellCost h g * QAlgorithms.effectProb
        (QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T))
        (QAlgorithms.conjSuperop (canonicalAction D g)
          (QAlgorithms.pureDensity (canonicalInput D x (fun _ => 1)))) = (ΦC (g⁻¹ * h)).re := by
    intro h
    simp only [ΦC]
    rw [eff_eq D hD x T h g, cost_eq htr h g, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  simp_rw [hpt]
  have hinv := integral_mul_left_eq_self (μ := dg) (fun m => (ΦC m).re) g⁻¹
  rw [hinv, show (∫ m, (ΦC m).re ∂dg) = (∫ m, ΦC m ∂dg).re from integral_re (integ dg ΦC hcont)]
  have hsum : ∫ m, ΦC m ∂dg = ∑ k : Fin d, ∑ l : Fin d, T k l * conj (x k) * x l *
      ((if k.val = l.val then 1 / 2 else 0) -
        ((if k.val + 1 = l.val then 1 else 0) + (if l.val + 1 = k.val then 1 else 0)) / 4) := by
    simp only [ΦC]
    have hint : ∀ k l : Fin d, Integrable (fun m : SU2 => T k l * conj (x k) * x l *
        ((weylCharacter (2 * (k.val + 1)) m * weylCharacter (2 * (l.val + 1)) m *
          (1 - weylCharacter 2 m ^ 2 / 4) : ℝ) : ℂ)) dg :=
      fun k l => integ dg _ (continuous_const.mul (hc2 k l))
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => hint k l)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun l _ => hint k l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, I_eq dg hW k.val l.val]
  rw [hsum]
  exact alg_eq x T

theorem conj2 [dg.IsMulLeftInvariant] (hD : IsSpinFamily D)
    (htr : ∀ m : SU2, ((((m : Matrix (Fin 2) (Fin 2) ℂ).trace.re : ℝ) : ℂ) =
      (m : Matrix (Fin 2) (Fin 2) ℂ).trace))
    (hW : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ∫ g, (weylCharacter a g : ℂ) * (weylCharacter b g : ℂ) ∂dg = if a = b then 1 else 0)
    (hne : ∀ s s', s ≠ s' → ∀ i i' m m',
      ∫ h, (D s).matrix h i i' * conj ((D s').matrix h m m') ∂dg = 0)
    (heq : ∀ s i i' m m', ∫ h, (D s).matrix h i i' * conj ((D s).matrix h m m') ∂dg =
      if i = m ∧ i' = m' then 1 / ((D s).dim : ℂ) else 0)
    (x : Fin d → ℂ) (T : Matrix (Fin d) (Fin d) ℂ) (hT : T.PosSemidef) (hT1 : ∀ k, T k k = 1) :
    ∃ M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) SU2,
      M.reference = dg ∧
      (∀ h, M.density h = QAlgorithms.conjSuperop (canonicalAction D h) (hayashiSeed D T)) ∧
      ∀ g : SU2, pointwiseRisk (canonicalAction D) bellCost
        (QAlgorithms.pureDensity (canonicalInput D x (fun _ => 1))) M g = hayashiError x T := by
  refine ⟨⟨dg, inferInstance, fun h => QAlgorithms.conjSuperop (canonicalAction D h)
    (hayashiSeed D T), measurable_F D T, fun h => ?_, integrable_F D dg T,
    integral_F D dg T hT1 hne heq⟩, rfl, fun h => rfl, fun g => ?_⟩
  · exact (seed_psd D T hT).mul_mul_conjTranspose_same _
  · exact risk_eq D dg hD htr hW x T g

end risk
end C2Aux

open MeasureTheory Filter Topology ParallelSU2.Reduction ComplexOrder ComplexConjugate in
theorem solution
    [IsTopologicalGroup SU2] [CompactSpace SU2] [MeasurableSpace SU2] [BorelSpace SU2]
    (dg : Measure SU2) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∀ d : ℕ, ∃ D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2,
      IsSpinFamily D) ∧
    (∀ (d : ℕ) (D : Fin d → QAlgorithms.Papers.Independent.Next46.P36.BasedIrrep SU2),
      IsSpinFamily D →
      ∀ x : Fin d → ℂ, ∑ k, Complex.normSq (x k) = 1 →
      ∀ T : Matrix (Fin d) (Fin d) ℂ, T.PosSemidef → (∀ k, T k k = 1) →
      ∃ M : QAlgorithms.Measurements.DensityPOVM
          (QAlgorithms.Papers.Independent.Next46.P36.CanonicalIndex D) SU2,
        M.reference = dg ∧
        (∀ h, M.density h = QAlgorithms.conjSuperop
          (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D h) (hayashiSeed D T)) ∧
        ∀ g : SU2,
          pointwiseRisk (QAlgorithms.Papers.Independent.Next46.P36.canonicalAction D)
              QAlgorithms.Papers.Independent.Next46.P36.bellCost
              (QAlgorithms.pureDensity
                (QAlgorithms.Papers.Independent.Next46.P36.canonicalInput D x (fun _ => 1))) M g =
              hayashiError x T ∧
          methodValue x ≤ hayashiError x T ∧
          (T = phaseAligned x → hayashiError x T = methodValue x)) ∧
    (∀ d : ℕ, 1 ≤ d →
      IsLeast {r : ℝ | ∃ x : Fin d → ℂ, ∑ k, Complex.normSq (x k) = 1 ∧ r = methodValue x}
        (Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2)) ∧
    Tendsto (fun d : ℕ => (2 * (d : ℝ) - 1) ^ 2 * Real.sin (Real.pi / (2 * (d : ℝ) + 2)) ^ 2)
      atTop (𝓝 (Real.pi ^ 2)) := by
  refine ⟨SymRepAux.spin_family_exists, ?_, ParallelSU2.Reduction.Aux.methodValue_isLeast,
    ParallelSU2.Reduction.Aux.scaled_limit⟩
  intro d D hD x hx T hT hT1
  have htr : ∀ m : SU2, ((((m : Matrix (Fin 2) (Fin 2) ℂ).trace.re : ℝ) : ℂ) =
      (m : Matrix (Fin 2) (Fin 2) ℂ).trace) := fun m =>
    SymRepAux.su2_trace_real _
      (Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp m.2).1)
      (Matrix.mem_specialUnitaryGroup_iff.mp m.2).2
  obtain ⟨M, h1, h2, h3⟩ := C2Aux.conj2 D dg hD htr (CharAux.weyl_orth dg)
    (fun s s' hss' i i' m m' => SchurAux.orth_ne dg (D s) (D s')
      (by rw [(hD s).1, (hD s').1]; intro h; exact hss' (Fin.ext (by omega))) i i' m m')
    (fun s i i' m m' => SchurAux.orth_eq dg (D s) i i' m m') x T hT hT1
  refine ⟨M, h1, h2, fun g => ⟨h3 g,
    ParallelSU2.Reduction.Aux.methodValue_le_hayashiError x hx T hT hT1, fun hTe => ?_⟩⟩
  rw [hTe]
  exact ParallelSU2.Reduction.Aux.hayashiError_phaseAligned x hx
