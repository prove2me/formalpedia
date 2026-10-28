-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P26.typical_projectors_accept
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:30:44.735996+00:00
-- url     : https://prove2.me/submissions/9677e908-2559-485d-802e-5d50b60dc50b

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

lemma sum_prod_pi' {R : Type} [CommSemiring R] {n : ℕ} (h : Fin n → B → R) :
    ∑ z : Fin n → B, ∏ k, h k (z k) = ∏ k, ∑ c, h k c := by
  have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset B)) h
  rw [Fintype.piFinset_univ] at this
  exact this.symm

def qv (E σ : Matrix B B ℂ) (b : B) : ℂ := ∑ a, ∑ c, conj (E a b) * σ a c * E c b

lemma qv_nonneg {E σ : Matrix B B ℂ} (h : σ.PosSemidef) (b : B) : 0 ≤ qv E σ b := by
  have := h.dotProduct_mulVec_nonneg (fun a => E a b)
  convert this using 1
  simp [qv, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma qv_sum {E : Matrix B B ℂ} (hE : E ∈ Matrix.unitaryGroup B ℂ) (σ : Matrix B B ℂ) :
    ∑ b, qv E σ b = σ.trace := by
  have h := (Matrix.mem_unitaryGroup_iff).mp hE
  -- h : E * star E = 1
  have h' : ∀ c a, ∑ b, E c b * conj (E a b) = if c = a then 1 else 0 := by
    intro c a
    have := congrFun (congrFun h c) a
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using this
  unfold qv
  calc ∑ b, ∑ a, ∑ c, conj (E a b) * σ a c * E c b
      = ∑ a, ∑ c, σ a c * ∑ b, E c b * conj (E a b) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _
        ring
    _ = σ.trace := by
        simp only [h']
        simp [Matrix.trace]

lemma qv_recon {E ρ : Matrix B B ℂ} (hE : E ∈ Matrix.unitaryGroup B ℂ) (lam : B → ℝ)
    (hρ : ∀ a b, ρ a b = ∑ z, (lam z : ℂ) * E a z * conj (E b z)) (b : B) :
    qv E ρ b = (lam b : ℂ) := by
  have h := (Matrix.mem_unitaryGroup_iff').mp hE
  have h' : ∀ z b, ∑ a, conj (E a b) * E a z = if b = z then 1 else 0 := by
    intro z b
    have := congrFun (congrFun h b) z
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using this
  unfold qv
  have : ∀ a c, ρ a c = ∑ z, (lam z : ℂ) * E a z * conj (E c z) := hρ
  simp_rw [this]
  calc ∑ a, ∑ c, conj (E a b) * (∑ z, (lam z : ℂ) * E a z * conj (E c z)) * E c b
      = ∑ a, ∑ c, ∑ z, (lam z : ℂ) * ((conj (E a b) * E a z) * (conj (E c z) * E c b)) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        ring
    _ = ∑ a, ∑ z, ∑ c, (lam z : ℂ) * ((conj (E a b) * E a z) * (conj (E c z) * E c b)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ z, ∑ a, ∑ c, (lam z : ℂ) * ((conj (E a b) * E a z) * (conj (E c z) * E c b)) :=
        Finset.sum_comm
    _ = ∑ z, (lam z : ℂ) * (∑ a, conj (E a b) * E a z) * (∑ c, conj (E c z) * E c b) := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [mul_assoc (lam z : ℂ), Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
    _ = lam b := by
        simp only [h']
        simp

lemma qv_add (E σ τ : Matrix B B ℂ) (b : B) : qv E (σ + τ) b = qv E σ b + qv E τ b := by
  simp only [qv, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma qv_smul (E σ : Matrix B B ℂ) (c : ℂ) (b : B) : qv E (c • σ) b = c * qv E σ b := by
  simp only [qv, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c' _ => ?_))
  ring

lemma qv_sum_fin {ι : Type} (s : Finset ι) (E : Matrix B B ℂ) (f : ι → Matrix B B ℂ) (b : B) :
    qv E (∑ j ∈ s, f j) b = ∑ j ∈ s, qv E (f j) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qv]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, qv_add, ih]

def wordState {n : ℕ} (σ : Fin n → Matrix B B ℂ) : Matrix (Fin n → B) (Fin n → B) ℂ :=
  Matrix.of fun a b => ∏ i, σ i (a i) (b i)

lemma trace_word {n : ℕ} (E σ : Fin n → Matrix B B ℂ) (acc : (Fin n → B) → Prop) :
    (spectralWordProjector E acc * wordState σ).trace =
      ∑ z : Fin n → B, if acc z then ∏ i, qv (E i) (σ i) (z i) else 0 := by
  have hM : ∀ a b, spectralWordProjector E acc a b =
      ∑ z : Fin n → B, if acc z then ∏ i, E i (a i) (z i) * conj (E i (b i) (z i)) else 0 :=
    fun a b => rfl
  have step : ∀ z : Fin n → B, ∑ a : Fin n → B, ∑ b : Fin n → B,
      (∏ i, E i (a i) (z i) * conj (E i (b i) (z i))) * ∏ i, σ i (b i) (a i) =
      ∏ i, qv (E i) (σ i) (z i) := by
    intro z
    have e1 : ∀ a b : Fin n → B, (∏ i, E i (a i) (z i) * conj (E i (b i) (z i))) * ∏ i, σ i (b i) (a i)
        = ∏ i, (E i (a i) (z i) * conj (E i (b i) (z i)) * σ i (b i) (a i)) := by
      intro a b; rw [← Finset.prod_mul_distrib]
    simp_rw [e1]
    have e2 : ∀ a : Fin n → B, ∑ b : Fin n → B,
        ∏ i, (E i (a i) (z i) * conj (E i (b i) (z i)) * σ i (b i) (a i)) =
        ∏ i, ∑ y, (E i (a i) (z i) * conj (E i y (z i)) * σ i y (a i)) := by
      intro a
      exact sum_prod_pi' (fun k y => E k (a k) (z k) * conj (E k y (z k)) * σ k y (a k))
    simp_rw [e2]
    rw [sum_prod_pi' (fun k x => ∑ y, (E k x (z k) * conj (E k y (z k)) * σ k y x))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    unfold qv
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    ring
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, hM, wordState, Matrix.of_apply]
  calc ∑ a : Fin n → B, ∑ b : Fin n → B,
        (∑ z : Fin n → B, if acc z then ∏ i, E i (a i) (z i) * conj (E i (b i) (z i)) else 0) *
          ∏ i, σ i (b i) (a i)
      = ∑ a : Fin n → B, ∑ z : Fin n → B, ∑ b : Fin n → B,
          if acc z then (∏ i, E i (a i) (z i) * conj (E i (b i) (z i))) * ∏ i, σ i (b i) (a i)
          else 0 := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun b _ => ?_))
        split_ifs <;> simp
    _ = ∑ z : Fin n → B, ∑ a : Fin n → B, ∑ b : Fin n → B,
          if acc z then (∏ i, E i (a i) (z i) * conj (E i (b i) (z i))) * ∏ i, σ i (b i) (a i)
          else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : acc z
        · simp only [hz, if_true]
          exact step z
        · simp [hz]


def wt {n : ℕ} (q : Fin n → B → ℝ) (z : Fin n → B) : ℝ := ∏ i, q i (z i)

lemma wt_sum {n : ℕ} (q : Fin n → B → ℝ) (hq : ∀ i, ∑ b, q i b = 1) :
    ∑ z, wt q z = 1 := by
  unfold wt
  rw [sum_prod_pi']
  simp [hq]

lemma wt_single {n : ℕ} (q : Fin n → B → ℝ) (hq : ∀ i, ∑ b, q i b = 1) (i : Fin n) (f : B → ℝ) :
    ∑ z, wt q z * f (z i) = ∑ c, q i c * f c := by
  have h : ∀ z : Fin n → B, wt q z * f (z i) = ∏ k, (q k (z k) * (if k = i then f (z k) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib]
    simp [wt]
  simp_rw [h]
  rw [sum_prod_pi' (fun k c => q k c * (if k = i then f c else 1))]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_one]
  · simp
  · intro k hk
    have : k ≠ i := Finset.ne_of_mem_erase hk
    simp [this, hq]

lemma wt_pair {n : ℕ} (q : Fin n → B → ℝ) (hq : ∀ i, ∑ b, q i b = 1) (i j : Fin n) (hij : i ≠ j)
    (f g : B → ℝ) :
    ∑ z, wt q z * (f (z i) * g (z j)) = (∑ c, q i c * f c) * (∑ c, q j c * g c) := by
  have h : ∀ z : Fin n → B, wt q z * (f (z i) * g (z j)) =
      ∏ k, (q k (z k) * ((if k = i then f (z k) else 1) * (if k = j then g (z k) else 1))) := by
    intro z
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp [wt]
  simp_rw [h]
  rw [sum_prod_pi' (fun k c => q k c * ((if k = i then f c else 1) * (if k = j then g c else 1)))]
  have key : ∀ k, ∑ c, q k c * ((if k = i then f c else 1) * (if k = j then g c else 1)) =
      (if k = i then ∑ c, q i c * f c else 1) * (if k = j then ∑ c, q j c * g c else 1) := by
    intro k
    by_cases hki : k = i
    · subst hki
      have : k ≠ j := hij
      simp [this]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj, hq]
  simp_rw [key]
  rw [Finset.prod_mul_distrib]
  simp

lemma cheb {n : ℕ} (q : Fin n → B → ℝ) (hq0 : ∀ i b, 0 ≤ q i b) (hq : ∀ i, ∑ b, q i b = 1)
    (S : Finset (Fin n)) (b : B) (s : ℝ) (hs : 0 < s) :
    ∑ z ∈ Finset.univ.filter
      (fun z : Fin n → B => s ≤ |((S.filter (fun i => z i = b)).card : ℝ) - ∑ i ∈ S, q i b|),
      wt q z ≤ (S.card : ℝ) / s ^ 2 := by
  classical
  have hw0 : ∀ z, 0 ≤ wt q z := fun z => Finset.prod_nonneg (fun i _ => hq0 i _)
  set Y : Fin n → B → ℝ := fun i c => (if c = b then 1 else 0) - q i b with hY
  have hD : ∀ z : Fin n → B, ((S.filter (fun i => z i = b)).card : ℝ) - ∑ i ∈ S, q i b
      = ∑ i ∈ S, Y i (z i) := by
    intro z
    rw [Finset.card_filter]
    push_cast
    simp [hY, Finset.sum_sub_distrib]
  have hq1 : ∀ i b, q i b ≤ 1 := by
    intro i b
    rw [← hq i]
    exact Finset.single_le_sum (fun c _ => hq0 i c) (Finset.mem_univ b)
  have hmom : ∑ z, wt q z * (∑ i ∈ S, Y i (z i)) ^ 2 ≤ S.card := by
    have e1 : ∀ z, wt q z * (∑ i ∈ S, Y i (z i)) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, wt q z * (Y i (z i) * Y j (z j)) := by
      intro z
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := S)]
    have e2 : ∀ i ∈ S, ∑ j ∈ S, ∑ z, wt q z * (Y i (z i) * Y j (z j)) ≤ 1 := by
      intro i hi
      rw [← Finset.add_sum_erase _ _ hi]
      have hz : ∑ j ∈ S.erase i, ∑ z, wt q z * (Y i (z i) * Y j (z j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [wt_pair q hq i j (Ne.symm hji)]
        have : ∑ c, q i c * Y i c = 0 := by
          simp only [hY, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_mul, hq]; simp
        rw [this]; simp
      rw [hz, add_zero]
      have : ∑ z, wt q z * (Y i (z i) * Y i (z i)) = ∑ c, q i c * (Y i c * Y i c) :=
        wt_single q hq i (fun c => Y i c * Y i c)
      rw [this]
      calc ∑ c, q i c * (Y i c * Y i c) ≤ ∑ c, q i c * 1 := by
            apply Finset.sum_le_sum
            intro c _
            apply mul_le_mul_of_nonneg_left _ (hq0 i c)
            have h1 := hq0 i b
            have h2 := hq1 i b
            by_cases hc : c = b <;> simp [hY, hc] <;> nlinarith
        _ = 1 := by simp [hq]
    calc _ ≤ ∑ i ∈ S, (1:ℝ) := Finset.sum_le_sum e2
      _ = S.card := by simp
  have hcheb : ∑ z ∈ Finset.univ.filter
      (fun z : Fin n → B => s ≤ |((S.filter (fun i => z i = b)).card : ℝ) - ∑ i ∈ S, q i b|),
      wt q z ≤ ∑ z, wt q z * (∑ i ∈ S, Y i (z i)) ^ 2 / s ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun z : Fin n → B => s ≤ |((S.filter (fun i => z i = b)).card : ℝ) - ∑ i ∈ S, q i b|)
      (fun z => wt q z * (∑ i ∈ S, Y i (z i)) ^ 2 / s ^ 2)]
    have h2 : 0 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin n → B => ¬ s ≤ |((S.filter (fun i => z i = b)).card : ℝ) - ∑ i ∈ S, q i b|), wt q z * (∑ i ∈ S, Y i (z i)) ^ 2 / s ^ 2 :=
      Finset.sum_nonneg (fun z _ => by have := hw0 z; positivity)
    refine le_trans ?_ (le_add_of_nonneg_right h2)
    apply Finset.sum_le_sum
    intro z hz
    rw [Finset.mem_filter] at hz
    have hz2 := hz.2
    rw [hD z] at hz2
    have : s ^ 2 ≤ (∑ i ∈ S, Y i (z i)) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg (∑ i ∈ S, Y i (z i)), neg_abs_le (∑ i ∈ S, Y i (z i))] : -|∑ i ∈ S, Y i (z i)| ≤ s) hz2
      nlinarith [sq_abs (∑ i ∈ S, Y i (z i))]
    rw [le_div_iff₀ (by positivity)]
    have := hw0 z
    nlinarith
  refine le_trans hcheb ?_
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hmom (by positivity)


def Acc {n : ℕ} {K : Type} [Fintype K] [DecidableEq K] (kf : Fin n → K) (r : K → B → ℝ) (δ : ℝ)
    (z : Fin n → B) : Prop :=
  (∀ i, 0 < r (kf i) (z i)) ∧ ∀ k, 0 < (Finset.univ.filter (fun i => kf i = k)).card → ∀ b,
    |(((Finset.univ.filter (fun i => kf i = k)).filter (fun i => z i = b)).card : ℝ) /
      (Finset.univ.filter (fun i => kf i = k)).card - r k b| ≤ δ

open Classical in
lemma block_accept {n : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    (q : Fin n → B → ℝ) (hq0 : ∀ i b, 0 ≤ q i b) (hq : ∀ i, ∑ b, q i b = 1)
    (kf : Fin n → K) (r : K → B → ℝ) (δ : ℝ) (hδ : 0 < δ) (m : ℝ) (hm : 0 < m)
    (hblock : ∀ k, 0 < (Finset.univ.filter (fun i => kf i = k)).card →
      m ≤ (Finset.univ.filter (fun i => kf i = k)).card ∧ ∀ b,
        |(∑ i ∈ Finset.univ.filter (fun i => kf i = k), q i b) /
          (Finset.univ.filter (fun i => kf i = k)).card - r k b| ≤ δ / 2)
    (hpos : ∀ i b, ¬ 0 < r (kf i) b → q i b = 0) :
    1 - 4 * Fintype.card K * Fintype.card B / (δ ^ 2 * m) ≤
      ∑ z ∈ Finset.univ.filter (fun z => Acc kf r δ z), wt q z := by
  classical
  have hw0 : ∀ z, 0 ≤ wt q z := fun z => Finset.prod_nonneg (fun i _ => hq0 i _)
  set Bad : K × B → (Fin n → B) → Prop := fun kb z =>
    0 < (Finset.univ.filter (fun i => kf i = kb.1)).card ∧
    δ < |(((Finset.univ.filter (fun i => kf i = kb.1)).filter (fun i => z i = kb.2)).card : ℝ) /
      (Finset.univ.filter (fun i => kf i = kb.1)).card - r kb.1 kb.2| with hBad
  have hcomp : ∑ z ∈ Finset.univ.filter (fun z => ¬ Acc kf r δ z), wt q z ≤
      ∑ kb : K × B, ∑ z ∈ Finset.univ.filter (fun z => Bad kb z), wt q z := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : Acc kf r δ z
    · simp only [hz, not_true_eq_false, if_false]
      exact Finset.sum_nonneg (fun kb _ => by split_ifs <;> simp [hw0 z])
    · simp only [hz, not_false_eq_true, if_true]
      unfold Acc at hz
      by_cases h1 : ∀ i, 0 < r (kf i) (z i)
      · have h2 : ∃ k, 0 < (Finset.univ.filter (fun i => kf i = k)).card ∧ ∃ b,
            δ < |(((Finset.univ.filter (fun i => kf i = k)).filter (fun i => z i = b)).card : ℝ) /
              (Finset.univ.filter (fun i => kf i = k)).card - r k b| := by
          by_contra hcon
          apply hz
          refine ⟨h1, fun k hk b => ?_⟩
          by_contra hb
          exact hcon ⟨k, hk, b, not_le.mp hb⟩
        obtain ⟨k, hk, b, hb⟩ := h2
        have hB : Bad (k, b) z := ⟨hk, hb⟩
        calc wt q z = (if Bad (k, b) z then wt q z else 0) := by rw [if_pos hB]
          _ ≤ _ := Finset.single_le_sum (f := fun kb => if Bad kb z then wt q z else 0)
              (fun kb _ => by split_ifs <;> simp [hw0 z]) (Finset.mem_univ (k, b))
      · push Not at h1
        obtain ⟨i, hi⟩ := h1
        have : wt q z = 0 := by
          unfold wt
          exact Finset.prod_eq_zero (Finset.mem_univ i) (hpos i (z i) (not_lt.mpr hi))
        rw [this]
        exact Finset.sum_nonneg (fun kb _ => by split_ifs <;> simp [hw0 z])
  have hone : ∑ z, wt q z = 1 := wt_sum q hq
  have hsplit : ∑ z ∈ Finset.univ.filter (fun z => Acc kf r δ z), wt q z +
      ∑ z ∈ Finset.univ.filter (fun z => ¬ Acc kf r δ z), wt q z = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hone
  have hbad : ∀ kb : K × B, ∑ z ∈ Finset.univ.filter (fun z => Bad kb z), wt q z ≤
      4 / (δ ^ 2 * m) := by
    intro kb
    by_cases hk : 0 < (Finset.univ.filter (fun i => kf i = kb.1)).card
    · set S := Finset.univ.filter (fun i => kf i = kb.1) with hS
      obtain ⟨hmS, hmean⟩ := hblock kb.1 hk
      have hSpos : (0:ℝ) < S.card := by exact_mod_cast hk
      have hs : 0 < δ * S.card / 2 := by positivity
      refine le_trans ?_ (?_ : (S.card : ℝ) / (δ * S.card / 2) ^ 2 ≤ 4 / (δ ^ 2 * m))
      · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hw0 z))
          (cheb q hq0 hq S kb.2 (δ * S.card / 2) hs)
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hb := hz.2.2
        have hm2 := hmean kb.2
        set c : ℝ := ((S.filter (fun i => z i = kb.2)).card : ℝ)
        set t : ℝ := ∑ i ∈ S, q i kb.2
        have h3 : δ / 2 < |c / S.card - t / S.card| := by
          have := abs_sub_abs_le_abs_sub (c / S.card - r kb.1 kb.2) (t / S.card - r kb.1 kb.2)
          have h4 : c / S.card - t / S.card = (c / S.card - r kb.1 kb.2) - (t / S.card - r kb.1 kb.2) := by ring
          rw [h4]
          linarith
        rw [← sub_div, abs_div, abs_of_pos hSpos, lt_div_iff₀ hSpos] at h3
        linarith
      · have : (S.card : ℝ) / (δ * S.card / 2) ^ 2 = 4 / (δ ^ 2 * S.card) := by
          field_simp
          norm_num
        rw [this]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_left hmS (by positivity)
    · have : Finset.univ.filter (fun z => Bad kb z) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro z _ hz
        exact hk hz.1
      rw [this]; simp only [Finset.sum_empty]; positivity
  have htot : ∑ kb : K × B, ∑ z ∈ Finset.univ.filter (fun z => Bad kb z), wt q z ≤
      4 * Fintype.card K * Fintype.card B / (δ ^ 2 * m) := by
    calc _ ≤ ∑ kb : K × B, 4 / (δ ^ 2 * m) := Finset.sum_le_sum (fun kb _ => hbad kb)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring
  linarith



lemma traceRight_density {α β : Type} [Fintype α] [Fintype β] {M : Matrix (α × β) (α × β) ℂ}
    (h : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.IsDensityMatrix (QAlgorithms.traceRight M) := by
  obtain ⟨hpsd, htr⟩ := h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hpsd
  obtain ⟨hherm, hnn⟩ := hpsd
  refine ⟨?_, ?_⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext j k
      simp only [Matrix.conjTranspose_apply, QAlgorithms.traceRight, Matrix.of_apply, star_sum]
      refine Finset.sum_congr rfl (fun h' _ => ?_)
      have := congrFun (congrFun hherm (j, h')) (k, h')
      simpa [Matrix.conjTranspose_apply] using this
    · have key : ∀ h' : β, star (fun p : α × β => if p.2 = h' then x p.1 else 0) ⬝ᵥ
          M.mulVec (fun p : α × β => if p.2 = h' then x p.1 else 0) =
          ∑ j, ∑ k, star (x j) * M (j, h') (k, h') * x k := by
        intro h'
        simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc,
          apply_ite (starRingEnd ℂ), ite_mul]
      have hsum : star x ⬝ᵥ (QAlgorithms.traceRight M).mulVec x =
          ∑ h' : β, star (fun p : α × β => if p.2 = h' then x p.1 else 0) ⬝ᵥ
          M.mulVec (fun p : α × β => if p.2 = h' then x p.1 else 0) := by
        simp_rw [key]
        have e : star x ⬝ᵥ (QAlgorithms.traceRight M).mulVec x =
            ∑ j, ∑ k, ∑ h' : β, star (x j) * M (j, h') (k, h') * x k := by
          simp only [dotProduct, Matrix.mulVec, QAlgorithms.traceRight, Matrix.of_apply, Pi.star_apply,
            Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun h' _ => ?_)))
          ring
        calc _ = _ := e
          _ = ∑ j, ∑ h' : β, ∑ k, star (x j) * M (j, h') (k, h') * x k :=
              Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
          _ = _ := Finset.sum_comm
      rw [hsum]
      exact Finset.sum_nonneg (fun h' _ => hnn _)
  · have : (QAlgorithms.traceRight M).trace = M.trace := by
      simp only [Matrix.trace, Matrix.diag_apply, QAlgorithms.traceRight, Matrix.of_apply]
      rw [Fintype.sum_prod_type]
    rw [this]; exact htr



lemma qv_real {E σ : Matrix B B ℂ} (h : σ.PosSemidef) (b : B) :
    qv E σ b = (((qv E σ b).re : ℝ) : ℂ) := by
  have := Complex.nonneg_iff.mp (qv_nonneg (E := E) h b)
  apply Complex.ext
  · simp
  · simp [← this.2]

lemma qv_re_nonneg {E σ : Matrix B B ℂ} (h : σ.PosSemidef) (b : B) : 0 ≤ (qv E σ b).re :=
  (Complex.nonneg_iff.mp (qv_nonneg (E := E) h b)).1

lemma qv_re_sum {E σ : Matrix B B ℂ} (hE : E ∈ Matrix.unitaryGroup B ℂ)
    (hσ : QAlgorithms.IsDensityMatrix σ) : ∑ b, (qv E σ b).re = 1 := by
  have h2 := congrArg Complex.re (qv_sum hE σ)
  rw [Complex.re_sum] at h2
  rw [h2, hσ.2]; simp

lemma qv_re_le_one {E σ : Matrix B B ℂ} (hE : E ∈ Matrix.unitaryGroup B ℂ)
    (hσ : QAlgorithms.IsDensityMatrix σ) (b : B) : (qv E σ b).re ≤ 1 := by
  rw [← qv_re_sum hE hσ]
  exact Finset.single_le_sum (f := fun b => (qv E σ b).re)
    (fun c _ => qv_re_nonneg hσ.1 c) (Finset.mem_univ b)

lemma effectProb_word {n : ℕ} (E σ : Fin n → Matrix B B ℂ)
    (hσ : ∀ i, QAlgorithms.IsDensityMatrix (σ i)) (acc : (Fin n → B) → Prop) :
    QAlgorithms.effectProb (spectralWordProjector E acc) (wordState σ) =
      ∑ z, if acc z then wt (fun i b => (qv (E i) (σ i) b).re) z else 0 := by
  unfold QAlgorithms.effectProb
  rw [trace_word, Complex.re_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  split_ifs
  · unfold wt
    rw [Finset.prod_congr rfl (fun i _ => qv_real (E := E i) (hσ i).1 (z i))]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  · simp

lemma prob_lower {n : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    (E σ : Fin n → Matrix B B ℂ) (hE : ∀ i, E i ∈ Matrix.unitaryGroup B ℂ)
    (hσ : ∀ i, QAlgorithms.IsDensityMatrix (σ i)) (acc : (Fin n → B) → Prop)
    (kf : Fin n → K) (r : K → B → ℝ) (δ : ℝ) (hδ : 0 < δ) (m : ℝ) (hm : 0 < m)
    (hacc : ∀ z, Acc kf r δ z → acc z)
    (hblock : ∀ k, 0 < (Finset.univ.filter (fun i => kf i = k)).card →
      m ≤ (Finset.univ.filter (fun i => kf i = k)).card ∧ ∀ b,
        |(∑ i ∈ Finset.univ.filter (fun i => kf i = k), (qv (E i) (σ i) b).re) /
          (Finset.univ.filter (fun i => kf i = k)).card - r k b| ≤ δ / 2)
    (hpos : ∀ i b, ¬ 0 < r (kf i) b → (qv (E i) (σ i) b).re = 0) :
    1 - 4 * Fintype.card K * Fintype.card B / (δ ^ 2 * m) ≤
      QAlgorithms.effectProb (spectralWordProjector E acc) (wordState σ) := by
  rw [effectProb_word E σ hσ acc]
  refine le_trans (block_accept (fun i b => (qv (E i) (σ i) b).re)
    (fun i b => qv_re_nonneg (hσ i).1 b) (fun i => qv_re_sum (hE i) (hσ i)) kf r δ hδ m hm
    hblock hpos) ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum (fun z _ => ?_)
  by_cases h : Acc kf r δ z
  · rw [if_pos h, if_pos (hacc z h)]
  · rw [if_neg h]
    split_ifs
    · exact Finset.prod_nonneg (fun i _ => qv_re_nonneg (hσ i).1 _)
    · exact le_refl _


lemma sum_fiber {ι A : Type} [Fintype ι] [Fintype A] [DecidableEq A] (w : ι → A) (f : A → ℝ) :
    ∑ i, f (w i) = ∑ x, ((Finset.univ.filter (fun i => w i = x)).card : ℝ) * f x := by
  rw [← Finset.sum_fiberwise Finset.univ w (fun i => f (w i))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have : ∀ i ∈ Finset.univ.filter (fun i => w i = x), f (w i) = f x := by
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl this]
  simp

lemma mean_close {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (hn : 0 < n) (w : Fin n → A)
    (p : A → ℝ) (η : ℝ)
    (hw : ∀ x, |((Finset.univ.filter fun i => w i = x).card : ℝ) / n - p x| ≤ η)
    (f : A → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |(∑ i, f (w i)) / n - ∑ x, p x * f x| ≤ Fintype.card A * η := by
  rw [sum_fiber, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc _ ≤ ∑ x : A, η := Finset.sum_le_sum (fun x _ => ?_)
    _ = _ := by simp
  have e : ((Finset.univ.filter fun i => w i = x).card : ℝ) * f x / n - p x * f x =
      (((Finset.univ.filter fun i => w i = x).card : ℝ) / n - p x) * f x := by ring
  rw [e, abs_mul, abs_of_nonneg (hf0 x)]
  calc _ ≤ η * 1 := mul_le_mul (hw x) (hf1 x) (hf0 x) (le_trans (abs_nonneg _) (hw x))
    _ = η := mul_one η

def sg (C : BroadcastChannel X B1 B2) (D : MartonData U V X) (u : U) (v : V) : Op B1 :=
  QAlgorithms.traceRight (C.rho (D.encode u v))

lemma sg_density (C : BroadcastChannel X B1 B2) (D : MartonData U V X) (u : U) (v : V) :
    QAlgorithms.IsDensityMatrix (sg C D u v) :=
  traceRight_density (C.density _)

lemma eig_eq (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D)) (b : B1) :
    Sbar.eigenvalue b = ∑ x : U × V, D.law.prob x * (qv (Sbar.basis : Op B1) (sg C D x.1 x.2) b).re := by
  have h := qv_recon (E := (Sbar.basis : Op B1)) (ρ := averageState1 C D) Sbar.basis.2
    Sbar.eigenvalue Sbar.reconstruct b
  have h2 := congrArg Complex.re h
  unfold averageState1 at h2
  rw [qv_sum_fin] at h2
  simp_rw [qv_sum_fin, qv_smul] at h2
  rw [Complex.re_sum] at h2
  simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re] at h2
  rw [Fintype.sum_prod_type]
  rw [← h2]
  rfl


lemma avg_part (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D)) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N : ℕ, 0 < N ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob η (fun i => (u i, v i)) →
        1 - ε ≤ QAlgorithms.effectProb (averagedProjector Sbar n δ) (receiver1Word C D u v) := by
  refine ⟨δ / (2 * ((Fintype.card U : ℝ) * Fintype.card V + 1)), by positivity,
    ⌈4 * (Fintype.card B1 : ℝ) / (δ ^ 2 * ε)⌉₊ + 1, Nat.succ_pos _, ?_⟩
  intro η hη hηle n hn u v hty
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨_, hfreq, hsupp⟩ := hty
  have hE : ∀ i : Fin n, (fun _ : Fin n => (Sbar.basis : Op B1)) i ∈ Matrix.unitaryGroup B1 ℂ :=
    fun _ => Sbar.basis.2
  have hσ : ∀ i : Fin n, QAlgorithms.IsDensityMatrix ((fun i => sg C D (u i) (v i)) i) :=
    fun i => sg_density C D (u i) (v i)
  have hS : (Finset.univ.filter (fun i : Fin n => (fun _ : Fin n => ()) i = ())) = Finset.univ := by
    ext i; simp
  have hpos' : (0 : ℝ) < (Fintype.card U : ℝ) * Fintype.card V + 1 := by positivity
  have hcardη : (Fintype.card (U × V) : ℝ) * η ≤ δ / 2 := by
    rw [Fintype.card_prod]; push_cast
    have : η * (2 * ((Fintype.card U : ℝ) * Fintype.card V + 1)) ≤ δ := by
      calc _ ≤ δ / (2 * ((Fintype.card U : ℝ) * Fintype.card V + 1)) *
            (2 * ((Fintype.card U : ℝ) * Fintype.card V + 1)) :=
            mul_le_mul_of_nonneg_right hηle (by positivity)
        _ = δ := by field_simp
    nlinarith [mul_pos hη hpos', (by positivity : (0:ℝ) ≤ (Fintype.card U : ℝ) * Fintype.card V)]
  have key := prob_lower (B := B1) (fun _ : Fin n => (Sbar.basis : Op B1))
    (fun i => sg C D (u i) (v i)) hE hσ (StrongTypical Sbar.eigenvalue δ)
    (fun _ : Fin n => ()) (fun _ b => Sbar.eigenvalue b) δ hδ n hnR
    (by
      intro z hz
      refine ⟨hn0, fun a => ?_, hz.1⟩
      have := hz.2 () (by rw [hS]; simpa using hn0) a
      rw [hS] at this
      simpa using this)
    (by
      intro k hk
      rw [hS]
      refine ⟨by simp, fun b => ?_⟩
      simp only [Finset.card_univ, Fintype.card_fin]
      have hmc := mean_close hn0 (fun i => (u i, v i)) D.law.prob η hfreq
        (fun x => (qv (Sbar.basis : Op B1) (sg C D x.1 x.2) b).re)
        (fun x => qv_re_nonneg (sg_density C D _ _).1 b)
        (fun x => qv_re_le_one Sbar.basis.2 (sg_density C D _ _) b)
      rw [← eig_eq C D Sbar b] at hmc
      exact le_trans hmc hcardη)
    (by
      intro i b hb
      by_contra hne
      have hge : 0 ≤ (qv (Sbar.basis : Op B1) (sg C D (u i) (v i)) b).re :=
        qv_re_nonneg (sg_density C D _ _).1 b
      have hgt : 0 < (qv (Sbar.basis : Op B1) (sg C D (u i) (v i)) b).re :=
        lt_of_le_of_ne hge (Ne.symm hne)
      apply hb
      rw [eig_eq C D Sbar b]
      have hp := hsupp i
      refine lt_of_lt_of_le (mul_pos hp hgt) ?_
      exact Finset.single_le_sum (f := fun x : U × V => D.law.prob x *
        (qv (Sbar.basis : Op B1) (sg C D x.1 x.2) b).re)
        (fun x _ => mul_nonneg (D.law.nonneg x) (qv_re_nonneg (sg_density C D _ _).1 b))
        (Finset.mem_univ (u i, v i)))
  refine le_trans ?_ key
  have : 4 * (Fintype.card Unit : ℝ) * Fintype.card B1 / (δ ^ 2 * n) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 4 * (Fintype.card B1 : ℝ) / (δ ^ 2 * ε) ≤ n := by
      have := Nat.le_ceil (4 * (Fintype.card B1 : ℝ) / (δ ^ 2 * ε))
      have h2 : ((⌈4 * (Fintype.card B1 : ℝ) / (δ ^ 2 * ε)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    simp only [Fintype.card_unit, Nat.cast_one]
    nlinarith
  linarith


lemma ratio_close {V' : Type} [Fintype V'] (N p g : V' → ℝ) (n η c : ℝ) (hn : 0 < n) (hη : 0 < η)
    (hp0 : ∀ x, 0 ≤ p x) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hN : ∀ x, |N x / n - p x| ≤ η) (hc : 0 < c) (hm : c ≤ ∑ x, p x)
    (hηc : (Fintype.card V' : ℝ) * η ≤ c / 2) :
    n * c / 2 ≤ ∑ x, N x ∧
    |(∑ x, N x * g x) / (∑ x, N x) - (∑ x, p x * g x) / (∑ x, p x)| ≤
      (Fintype.card V' : ℝ) * (2 * η * (1 + Fintype.card V') / c) := by
  set M := ∑ x, N x with hM
  set m := ∑ x, p x with hmdef
  have hNn : ∀ x, |N x - n * p x| ≤ n * η := by
    intro x
    have h := hN x
    have : N x - n * p x = n * (N x / n - p x) := by field_simp
    rw [this, abs_mul, abs_of_pos hn]
    exact mul_le_mul_of_nonneg_left h hn.le
  have hMm : |M - n * m| ≤ n * (Fintype.card V' * η) := by
    have : M - n * m = ∑ x, (N x - n * p x) := by
      rw [hM, hmdef, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [this]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc _ ≤ ∑ x : V', n * η := Finset.sum_le_sum (fun x _ => hNn x)
      _ = _ := by simp; ring
  have hMlow : n * c / 2 ≤ M := by
    have h1 := (abs_le.mp hMm).1
    have h2 : n * (Fintype.card V' * η) ≤ n * (c / 2) := mul_le_mul_of_nonneg_left hηc hn.le
    nlinarith
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hMlow
  have hmpos : 0 < m := lt_of_lt_of_le hc hm
  refine ⟨hMlow, ?_⟩
  set θ : ℝ := 2 * η * (1 + Fintype.card V') / c with hθ
  have hterm : ∀ x, |N x / M - p x / m| ≤ θ := by
    intro x
    have hpx : p x ≤ m := Finset.single_le_sum (f := p) (fun y _ => hp0 y) (Finset.mem_univ x)
    have e : N x / M - p x / m = ((N x - n * p x) * m + p x * (n * m - M)) / (M * m) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos hMpos hmpos), div_le_iff₀ (mul_pos hMpos hmpos)]
    have h1 : |(N x - n * p x) * m + p x * (n * m - M)| ≤
        n * η * m + p x * (n * (Fintype.card V' * η)) := by
      refine le_trans (abs_add_le _ _) ?_
      refine add_le_add ?_ ?_
      · rw [abs_mul, abs_of_pos hmpos]
        exact mul_le_mul_of_nonneg_right (hNn x) hmpos.le
      · rw [abs_mul, abs_of_nonneg (hp0 x), abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hMm (hp0 x)
    refine le_trans h1 ?_
    have h3 : p x * (n * (Fintype.card V' * η)) ≤ m * (n * (Fintype.card V' * η)) :=
      mul_le_mul_of_nonneg_right hpx (by positivity)
    have : θ * (M * m) ≥ θ * (n * c / 2 * m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMlow hmpos.le) (by positivity)
    have h4 : θ * (n * c / 2 * m) = n * η * m * (1 + Fintype.card V') := by
      rw [hθ]; field_simp
    nlinarith
  have : (∑ x, N x * g x) / M - (∑ x, p x * g x) / m = ∑ x, (N x / M - p x / m) * g x := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [this]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc _ ≤ ∑ x : V', θ := Finset.sum_le_sum (fun x _ => ?_)
    _ = _ := by simp
  rw [abs_mul, abs_of_nonneg (hg0 x)]
  calc _ ≤ θ * 1 := mul_le_mul (hterm x) (hg1 x) (hg0 x) (le_trans (abs_nonneg _) (hterm x))
    _ = θ := mul_one θ


lemma cond_qv (C : BroadcastChannel X B1 B2) (D : MartonData U V X) (E : Op B1) (a : U)
    (hm : 0 < ∑ v, D.law.prob (a, v)) (b : B1) :
    (qv E (conditionalState1 C D a) b).re =
      (∑ v, D.law.prob (a, v) * (qv E (sg C D a v) b).re) / ∑ v, D.law.prob (a, v) := by
  have hc : conditionalState1 C D a = (((∑ v, D.law.prob (a, v) : ℝ)⁻¹ : ℝ) : ℂ) •
      ∑ v, (D.law.prob (a, v) : ℂ) • sg C D a v := by
    unfold conditionalState1
    simp only []
    rw [if_pos hm]
    simp [sg]
  rw [hc, qv_smul, qv_sum_fin]
  simp_rw [qv_smul]
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
  rw [div_eq_inv_mul]

lemma cond_eig (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) (a : U)
    (hm : 0 < ∑ v, D.law.prob (a, v)) (b : B1) :
    (Scond a).eigenvalue b =
      (∑ v, D.law.prob (a, v) * (qv ((Scond a).basis : Op B1) (sg C D a v) b).re) /
        ∑ v, D.law.prob (a, v) := by
  have h := qv_recon (E := ((Scond a).basis : Op B1)) (ρ := conditionalState1 C D a)
    (Scond a).basis.2 (Scond a).eigenvalue (Scond a).reconstruct b
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h2
  rw [← h2]
  exact (cond_qv C D _ a hm b).symm.symm

lemma exists_pmin (m : U → ℝ) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ u, 0 < m u → c ≤ m u := by
  classical
  by_cases h : (Finset.univ.filter (fun u => 0 < m u)).Nonempty
  · obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image _ m h
    refine ⟨min (m u0) 1, lt_min (Finset.mem_filter.mp hu0).2 one_pos, min_le_right _ _, ?_⟩
    intro u hu
    exact le_trans (min_le_left _ _) (hmin u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
  · refine ⟨1, one_pos, le_refl _, ?_⟩
    intro u hu
    exact absurd ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩ h


lemma sum_fiber_s {ι A : Type} [Fintype A] [DecidableEq A] (s : Finset ι) (w : ι → A)
    (f : A → ℝ) :
    ∑ i ∈ s, f (w i) = ∑ x, ((s.filter (fun i => w i = x)).card : ℝ) * f x := by
  rw [← Finset.sum_fiberwise s w (fun i => f (w i))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have : ∀ i ∈ s.filter (fun i => w i = x), f (w i) = f x := by
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl this]
  simp

lemma cond_part (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ N : ℕ, 0 < N ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob η (fun i => (u i, v i)) →
        1 - ε ≤ QAlgorithms.effectProb (conditionalTypicalProjector C D Scond u δ)
          (receiver1Word C D u v) := by
  obtain ⟨c, hc0, hc1, hcmin⟩ := exists_pmin (fun a : U => ∑ v, D.law.prob (a, v))
  have hk : (0 : ℝ) < (Fintype.card V : ℝ) + 1 := by positivity
  refine ⟨min (c / (2 * ((Fintype.card V : ℝ) + 1)))
      (δ * c / (4 * ((Fintype.card V : ℝ) + 1) ^ 2)), ?_,
    ⌈8 * (Fintype.card U : ℝ) * Fintype.card B1 / (δ ^ 2 * ε * c)⌉₊ + 1, Nat.succ_pos _, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  intro η hη hηle n hn u v hty
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨_, hfreq, hsupp⟩ := hty
  have hη1 : η ≤ c / (2 * ((Fintype.card V : ℝ) + 1)) := le_trans hηle (min_le_left _ _)
  have hη2 : η ≤ δ * c / (4 * ((Fintype.card V : ℝ) + 1) ^ 2) := le_trans hηle (min_le_right _ _)
  have hE : ∀ i : Fin n, (fun i => ((Scond (u i)).basis : Op B1)) i ∈ Matrix.unitaryGroup B1 ℂ :=
    fun i => (Scond (u i)).basis.2
  have hσ : ∀ i : Fin n, QAlgorithms.IsDensityMatrix ((fun i => sg C D (u i) (v i)) i) :=
    fun i => sg_density C D (u i) (v i)
  have hmass : ∀ i : Fin n, 0 < ∑ x, D.law.prob (u i, x) := fun i =>
    lt_of_lt_of_le (hsupp i) (Finset.single_le_sum (f := fun x => D.law.prob (u i, x))
      (fun x _ => D.law.nonneg _) (Finset.mem_univ (v i)))
  have key := prob_lower (B := B1) (fun i => ((Scond (u i)).basis : Op B1))
    (fun i => sg C D (u i) (v i)) hE hσ
    (ConditionalSpectralTypical (fun a => (Scond a).eigenvalue) δ u)
    u (fun a b => (Scond a).eigenvalue b) δ hδ (n * c / 2) (by positivity)
    (fun z hz => hz)
    (by
      intro a ha
      obtain ⟨i0, hi0⟩ := Finset.card_pos.mp ha
      have hi0' : u i0 = a := (Finset.mem_filter.mp hi0).2
      have hma : 0 < ∑ x, D.law.prob (a, x) := by rw [← hi0']; exact hmass i0
      have hca : c ≤ ∑ x, D.law.prob (a, x) := hcmin a hma
      set S := Finset.univ.filter (fun i : Fin n => u i = a) with hS
      have hNx : ∀ x, |((S.filter (fun i => v i = x)).card : ℝ) / n - D.law.prob (a, x)| ≤ η := by
        intro x
        have := hfreq (a, x)
        have e : (Finset.univ.filter fun i : Fin n => (u i, v i) = (a, x)) =
            S.filter (fun i => v i = x) := by
          ext i; simp [hS, Prod.ext_iff]
        rw [e] at this
        exact this
      have hηc : (Fintype.card V : ℝ) * η ≤ c / 2 := by
        calc _ ≤ ((Fintype.card V : ℝ) + 1) * (c / (2 * ((Fintype.card V : ℝ) + 1))) :=
              mul_le_mul (by linarith) hη1 hη.le hk.le
          _ = c / 2 := by field_simp
      have hScard : (S.card : ℝ) = ∑ x, ((S.filter (fun i => v i = x)).card : ℝ) := by
        have := sum_fiber_s S v (fun _ => (1:ℝ))
        simpa using this
      have hrc := fun (b : B1) => ratio_close
        (fun x => ((S.filter (fun i => v i = x)).card : ℝ))
        (fun x => D.law.prob (a, x))
        (fun x => (qv ((Scond a).basis : Op B1) (sg C D a x) b).re) n η c hnR hη
        (fun x => D.law.nonneg _) (fun x => qv_re_nonneg (sg_density C D _ _).1 b)
        (fun x => qv_re_le_one (Scond a).basis.2 (sg_density C D _ _) b) hNx hc0 hca hηc
      refine ⟨?_, fun b => ?_⟩
      · rw [hScard]
        exact (hrc (Classical.choice C.output1_nonempty)).1
      · have h1 := (hrc b).2
        have hsum : ∑ i ∈ S, (qv ((Scond (u i)).basis : Op B1) (sg C D (u i) (v i)) b).re =
            ∑ x, ((S.filter (fun i => v i = x)).card : ℝ) *
              (qv ((Scond a).basis : Op B1) (sg C D a x) b).re := by
          rw [← sum_fiber_s S v (fun x => (qv ((Scond a).basis : Op B1) (sg C D a x) b).re)]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have : u i = a := (Finset.mem_filter.mp hi).2
          subst this; rfl
        show |(∑ i ∈ S, (qv ((Scond (u i)).basis : Op B1) (sg C D (u i) (v i)) b).re) / S.card -
          (Scond a).eigenvalue b| ≤ δ / 2
        rw [hsum, hScard, cond_eig C D Scond a hma b]
        refine le_trans h1 ?_
        have h4 : η * (4 * ((Fintype.card V : ℝ) + 1) ^ 2) ≤ δ * c := by
          rwa [le_div_iff₀ (by positivity)] at hη2
        have h5 : (Fintype.card V : ℝ) * (1 + Fintype.card V) ≤ ((Fintype.card V : ℝ) + 1) ^ 2 := by
          nlinarith [(by positivity : (0:ℝ) ≤ Fintype.card V)]
        rw [← mul_div_assoc, div_le_iff₀ hc0]
        nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 * η)])
    (by
      intro i b hb
      by_contra hne
      have hge : 0 ≤ (qv ((Scond (u i)).basis : Op B1) (sg C D (u i) (v i)) b).re :=
        qv_re_nonneg (sg_density C D _ _).1 b
      have hgt : 0 < (qv ((Scond (u i)).basis : Op B1) (sg C D (u i) (v i)) b).re :=
        lt_of_le_of_ne hge (Ne.symm hne)
      apply hb
      show 0 < (Scond (u i)).eigenvalue b
      rw [cond_eig C D Scond (u i) (hmass i) b]
      refine div_pos ?_ (hmass i)
      exact lt_of_lt_of_le (mul_pos (hsupp i) hgt) (Finset.single_le_sum
        (f := fun x => D.law.prob (u i, x) *
          (qv ((Scond (u i)).basis : Op B1) (sg C D (u i) x) b).re)
        (fun x _ => mul_nonneg (D.law.nonneg _) (qv_re_nonneg (sg_density C D _ _).1 b))
        (Finset.mem_univ (v i))))
  refine le_trans ?_ key
  have : 4 * (Fintype.card U : ℝ) * Fintype.card B1 / (δ ^ 2 * (n * c / 2)) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 8 * (Fintype.card U : ℝ) * Fintype.card B1 / (δ ^ 2 * ε * c) ≤ n := by
      have := Nat.le_ceil (8 * (Fintype.card U : ℝ) * Fintype.card B1 / (δ ^ 2 * ε * c))
      have h2 : ((⌈8 * (Fintype.card U : ℝ) * Fintype.card B1 / (δ ^ 2 * ε * c)⌉₊ + 1 : ℕ) : ℝ)
          ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  linarith


theorem typical_projectors_accept_main (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D))
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ deltaBar : ℝ, 0 < deltaBar → ∀ deltaCond : ℝ, 0 < deltaCond →
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob eta (fun i => (u i, v i)) →
        1 - epsilon ≤ effectProb (averagedProjector Sbar n deltaBar) (receiver1Word C D u v) ∧
        1 - epsilon ≤ effectProb (conditionalTypicalProjector C D Scond u deltaCond)
          (receiver1Word C D u v) := by
  intro ε hε hε1 δB hδB δC hδC
  obtain ⟨η1, hη1, N1, hN1, h1⟩ := avg_part C D Sbar ε hε δB hδB
  obtain ⟨η2, hη2, N2, hN2, h2⟩ := cond_part C D Scond ε hε δC hδC
  refine ⟨min η1 η2, lt_min hη1 hη2, max N1 N2, lt_max_of_lt_left hN1, ?_⟩
  intro n hn u v hty
  exact ⟨h1 _ (lt_min hη1 hη2) (min_le_left _ _) n (le_trans (le_max_left _ _) hn) u v hty,
    h2 _ (lt_min hη1 hη2) (min_le_right _ _) n (le_trans (le_max_right _ _) hn) u v hty⟩

end QAlgorithms.Papers.Independent.Support50.P26

section SolutionSection

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P26

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

theorem solution (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D))
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ deltaBar : ℝ, 0 < deltaBar → ∀ deltaCond : ℝ, 0 < deltaCond →
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob eta (fun i => (u i, v i)) →
        1 - epsilon ≤ QAlgorithms.effectProb (averagedProjector Sbar n deltaBar)
          (receiver1Word C D u v) ∧
        1 - epsilon ≤ QAlgorithms.effectProb (conditionalTypicalProjector C D Scond u deltaCond)
          (receiver1Word C D u v) :=
  typical_projectors_accept_main C D Sbar Scond

end SolutionSection

end

