-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P14.binary_scheme
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T21:05:15.532749+00:00
-- url     : https://prove2.me/submissions/0568d71f-4b94-468e-b3fa-0ebe5c13d4d2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P14
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Next46.P14

theorem g63d_map_equiv {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (σ : α ≃ β) : (PMF.uniformOfFintype α).map σ = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (σ.symm b)]
  · simp [Fintype.card_congr σ]
  · intro a ha
    have : b ≠ σ a := fun h => ha (by simp [h])
    simp [this]

theorem g63d_prod_unif {A B X Y : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A → X) (g : B → Y) (a : X) (c : Y) :
    (PMF.uniformOfFintype (A × B)).map (fun p => (f p.1, g p.2)) (a, c) =
      (PMF.uniformOfFintype (A × B)).map (fun p => f p.1) a *
        (PMF.uniformOfFintype (A × B)).map (fun p => g p.2) c := by
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, tsum_fintype, Fintype.card_prod]
  have hA : (Fintype.card A : ℝ≥0∞) ≠ 0 := by simp
  have hB : (Fintype.card B : ℝ≥0∞) ≠ 0 := by simp
  have hinv : ((Fintype.card A * Fintype.card B : ℕ) : ℝ≥0∞)⁻¹ =
      (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹ := by
    push_cast
    exact ENNReal.mul_inv (Or.inl hA) (Or.inl (by simp))
  have hBs : ∑ _y : B, (Fintype.card B : ℝ≥0∞)⁻¹ = 1 := by
    simp [Finset.sum_const, Finset.card_univ]
    exact ENNReal.mul_inv_cancel hB (by simp)
  have hAs : ∑ _y : A, (Fintype.card A : ℝ≥0∞)⁻¹ = 1 := by
    simp [Finset.sum_const, Finset.card_univ]
    exact ENNReal.mul_inv_cancel hA (by simp)
  rw [hinv]
  simp only [Fintype.sum_prod_type]
  have e1 : ∀ x y, (if (a, c) = (f x, g y) then (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹ else 0)
      = (if a = f x then (Fintype.card A : ℝ≥0∞)⁻¹ else 0) * (if c = g y then (Fintype.card B : ℝ≥0∞)⁻¹ else 0) := by
    intro x y; simp only [Prod.mk.injEq]; split_ifs <;> simp_all
  have e2 : ∀ (x : A), (if a = f x then (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹ else 0)
      = (if a = f x then (Fintype.card A : ℝ≥0∞)⁻¹ else 0) * (Fintype.card B : ℝ≥0∞)⁻¹ := by
    intro x; split_ifs <;> simp
  have e3 : ∀ (y : B), (if c = g y then (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹ else 0)
      = (Fintype.card A : ℝ≥0∞)⁻¹ * (if c = g y then (Fintype.card B : ℝ≥0∞)⁻¹ else 0) := by
    intro y; split_ifs <;> simp
  simp only [e1, e2, e3, ← Finset.mul_sum, ← Finset.sum_mul, hBs, mul_one]
  have hcancel : ∀ z : ℝ≥0∞, (Fintype.card A : ℝ≥0∞)⁻¹ * ((Fintype.card A : ℝ≥0∞) * z) = z := by
    intro z; rw [← mul_assoc, ENNReal.inv_mul_cancel hA (by simp), one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcancel]

theorem g63d_indep_equiv {Ω A B X Y : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (τ : Ω ≃ A × B) (U : Ω → X) (V : Ω → Y) (f : A → X) (g : B → Y)
    (hU : ∀ x, U x = f (τ x).1) (hV : ∀ x, V x = g (τ x).2) :
    Independent (PMF.uniformOfFintype Ω) U V := by
  intro a c
  have h1 : (PMF.uniformOfFintype Ω).map (fun x => (U x, V x)) =
      ((PMF.uniformOfFintype Ω).map τ).map (fun p => (f p.1, g p.2)) := by
    rw [PMF.map_comp]; congr 1; funext x; simp [hU, hV]
  have h2 : (PMF.uniformOfFintype Ω).map U =
      ((PMF.uniformOfFintype Ω).map τ).map (fun p => f p.1) := by
    rw [PMF.map_comp]; congr 1; funext x; simp [hU]
  have h3 : (PMF.uniformOfFintype Ω).map V =
      ((PMF.uniformOfFintype Ω).map τ).map (fun p => g p.2) := by
    rw [PMF.map_comp]; congr 1; funext x; simp [hV]
  rw [h1, h2, h3, g63d_map_equiv]
  exact g63d_prod_unif f g a c

theorem g63d_indep_map {Ω O X Y : Type*} (P : PMF Ω) (E : Ω → O) (U : O → X) (V : O → Y) :
    Independent (P.map E) U V ↔ Independent P (U ∘ E) (V ∘ E) := by
  unfold Independent
  simp only [PMF.map_comp]
  rfl

theorem g63d_ent_unif_map (p : ℕ) {A : Type*} [Fintype A] [Nonempty A] (f : A → ℕ)
    (hf : Function.Injective f) :
    spirEntropy p ((PMF.uniformOfFintype A).map f) =
      ENNReal.ofReal (Real.log (Fintype.card A) / Real.log p) := by
  unfold spirEntropy
  have hval : ∀ a, ((PMF.uniformOfFintype A).map f) (f a) = (Fintype.card A : ℝ≥0∞)⁻¹ := by
    intro a
    rw [PMF.map_apply, tsum_eq_single a]
    · simp
    · intro b hb; simp [hf.ne hb |>.symm]
  have hzero : ∀ n, n ∉ Set.range f → ((PMF.uniformOfFintype A).map f) n = 0 := by
    intro n hn
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun a => ?_
    have : n ≠ f a := fun h => hn ⟨a, h.symm⟩
    simp [this]
  rw [← hf.tsum_eq]
  · have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have hs : ∀ a, ENNReal.ofReal (-(((PMF.uniformOfFintype A).map f) (f a)).toReal *
        Real.log ((((PMF.uniformOfFintype A).map f) (f a)).toReal) / Real.log p) =
        ENNReal.ofReal ((Fintype.card A : ℝ)⁻¹ * Real.log (Fintype.card A) / Real.log p) := by
      intro a
      rw [hval]
      congr 1
      simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.log_inv]
      ring
    simp only [hs, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  · intro n hn
    by_contra h
    apply hn
    simp [hzero n h]

def g63d_e {N : ℕ} (n : Fin N) (row : Fin (N - 1) → ZMod 2) : ZMod 2 :=
  ∑ i, (if n.val = i.val + 1 then 1 else 0) * row i

theorem g63d_ans_flip {K N : ℕ} (k : Fin K) (n : Fin N) (h v : BinaryArray K N) (s : ZMod 2) :
    binaryAnswer (binaryQuery k n h) v s = binaryAnswer h v s + g63d_e n (v k) := by
  have hE : (∑ j, ∑ i, (if j = k ∧ n.val = i.val + 1 then (1 : ZMod 2) else 0) * v j i) =
      g63d_e n (v k) := by
    rw [Finset.sum_eq_single k]
    · simp [g63d_e]
    · intro j _ hj; simp [hj]
    · simp
  unfold binaryAnswer binaryQuery
  simp only [add_mul, Finset.sum_add_distrib, hE]
  ring

theorem g63d_e_zero {N : ℕ} (hN : 0 < N) (row : Fin (N - 1) → ZMod 2) :
    g63d_e (⟨0, hN⟩ : Fin N) row = 0 := by
  simp [g63d_e]

theorem g63d_e_succ {N : ℕ} (i : Fin (N - 1)) (hi : i.val + 1 < N) (row : Fin (N - 1) → ZMod 2) :
    g63d_e (⟨i.val + 1, hi⟩ : Fin N) row = row i := by
  unfold g63d_e
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : ¬ (i.val + 1 = j.val + 1) := fun h => hj (Fin.ext (by omega))
    simp only [this, if_false, zero_mul]
  · simp

theorem g63d_two : (1 : ZMod 2) + 1 = 0 := by decide

def g63d_flip {K N : ℕ} (k : Fin K) (n : Fin N) : BinaryArray K N ≃ BinaryArray K N where
  toFun := binaryQuery k n
  invFun := binaryQuery k n
  left_inv h := by
    funext j i; unfold binaryQuery; split_ifs <;> simp [add_assoc, g63d_two]
  right_inv h := by
    funext j i; unfold binaryQuery; split_ifs <;> simp [add_assoc, g63d_two]

theorem g63d_bin_c1 (K N : ℕ) (hN : 2 ≤ N) (k : Fin K) (w h : BinaryArray K N) (s : ZMod 2)
    (i : Fin (N - 1)) :
    binaryAnswer (binaryQuery k (⟨i.val + 1, by omega⟩ : Fin N) h) w s -
        binaryAnswer (binaryQuery k (⟨0, by omega⟩ : Fin N) h) w s = w k i := by
  rw [g63d_ans_flip, g63d_ans_flip, g63d_e_zero, g63d_e_succ]
  ring

theorem g63d_bin_c2 (K N : ℕ) (hK : 2 ≤ K) (hN : 2 ≤ N) (k k2 : Fin K) (n : Fin N) :
    (spirBinaryLaw K N).map (binaryServerView k n) =
      (spirBinaryLaw K N).map (binaryServerView k2 n) := by
  have : Nonempty (BinaryArray K N × BinaryArray K N × ZMod 2) := ⟨0⟩
  let G : BinaryArray K N × BinaryArray K N × ZMod 2 → _ :=
    fun x => (x.2.1, binaryAnswer x.2.1 x.1 x.2.2, x.1, x.2.2)
  have key : ∀ k' : Fin K, (spirBinaryLaw K N).map (binaryServerView k' n) =
      (spirBinaryLaw K N).map G := by
    intro k'
    let σ := (Equiv.refl (BinaryArray K N)).prodCongr ((g63d_flip k' n).prodCongr (Equiv.refl (ZMod 2)))
    have : binaryServerView k' n = G ∘ σ := rfl
    rw [this, ← PMF.map_comp]
    unfold spirBinaryLaw
    rw [g63d_map_equiv]
  rw [key, key]

def g63d_tau1 {K N : ℕ} (k : Fin K) : (BinaryArray K N × BinaryArray K N × ZMod 2) ≃
    (({j // j ≠ k} → Fin (N - 1) → ZMod 2) × ((Fin (N - 1) → ZMod 2) × BinaryArray K N × ZMod 2)) where
  toFun x := ((Equiv.piSplitAt k _ x.1).2, (x.1 k, x.2.1, x.2.2 + binaryAnswer x.2.1 x.1 0))
  invFun y := ((Equiv.piSplitAt k _).symm (y.2.1, y.1), y.2.2.1,
    y.2.2.2 - binaryAnswer y.2.2.1 ((Equiv.piSplitAt k _).symm (y.2.1, y.1)) 0)
  left_inv x := by
    obtain ⟨w, h, s⟩ := x
    have : (Equiv.piSplitAt k _).symm (w k, (Equiv.piSplitAt k _ w).2) = w :=
      (Equiv.piSplitAt k (fun _ => Fin (N - 1) → ZMod 2)).symm_apply_apply w
    simp only [this, add_sub_cancel_right]
  right_inv y := by
    obtain ⟨u, a, h, s⟩ := y
    have := (Equiv.piSplitAt k (fun _ => Fin (N - 1) → ZMod 2)).apply_symm_apply (a, u)
    simp only [Prod.ext_iff] at this
    have h1 : (Equiv.piSplitAt k (fun _ => Fin (N - 1) → ZMod 2)).symm (a, u) k = a := this.1
    have h2 := this.2
    simp only [h1, h2, sub_add_cancel]

theorem g63d_bin_c3 (K N : ℕ) (hK : 2 ≤ K) (hN : 2 ≤ N) (k : Fin K) :
    Independent (spirBinaryLaw K N) (binaryUndesired k) (binaryUserView k) := by
  have : Nonempty (BinaryArray K N × BinaryArray K N × ZMod 2) := ⟨0⟩
  unfold spirBinaryLaw
  refine g63d_indep_equiv (g63d_tau1 k) _ _ id
    (fun y : (Fin (N - 1) → ZMod 2) × BinaryArray K N × ZMod 2 =>
      (fun n : Fin N => binaryQuery k n y.2.1, fun n : Fin N => y.2.2 + g63d_e n y.1, y.2.1))
    (fun x => rfl) (fun x => ?_)
  obtain ⟨w, h, s⟩ := x
  simp only [binaryUserView, g63d_tau1, Equiv.coe_fn_mk, Prod.mk.injEq, and_true, true_and]
  funext n
  rw [g63d_ans_flip]
  unfold binaryAnswer
  ring

theorem g63d_ent_unif (p : ℕ) {A : Type*} [Fintype A] [Nonempty A] :
    spirEntropy p (PMF.uniformOfFintype A) =
      ENNReal.ofReal (Real.log (Fintype.card A) / Real.log p) := by
  unfold spirEntropy
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hs : ∀ a, ENNReal.ofReal (-((PMF.uniformOfFintype A) a).toReal *
      Real.log (((PMF.uniformOfFintype A) a).toReal) / Real.log p) =
      ENNReal.ofReal ((Fintype.card A : ℝ)⁻¹ * Real.log (Fintype.card A) / Real.log p) := by
    intro a
    rw [PMF.uniformOfFintype_apply]
    congr 1
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Real.log_inv]
    ring
  simp only [hs, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc.le]
  congr 1
  field_simp

def g63d_enc {α : Type*} [Fintype α] (a : α) : ℕ := (Fintype.equivFin α a : ℕ)

def g63d_dec {α : Type*} [Fintype α] [Inhabited α] (n : ℕ) : α :=
  if h : n < Fintype.card α then (Fintype.equivFin α).symm ⟨n, h⟩ else default

theorem g63d_dec_enc {α : Type*} [Fintype α] [Inhabited α] (a : α) :
    (g63d_dec (g63d_enc a) : α) = a := by
  unfold g63d_dec g63d_enc
  rw [dif_pos (Fintype.equivFin α a).isLt]
  simp

theorem g63d_enc_inj {α : Type*} [Fintype α] : Function.Injective (g63d_enc : α → ℕ) := by
  intro a b h
  unfold g63d_enc at h
  exact (Fintype.equivFin α).injective (Fin.ext h)

def g63d_idx {N r : ℕ} (c : Fin r) (i : Fin (N - 1)) : Fin (1 * (r * (N - 1))) :=
  ⟨c.val * (N - 1) + i.val, by
    have hc := c.2; have hi := i.2
    rw [one_mul]
    calc c.val * (N - 1) + i.val < c.val * (N - 1) + (N - 1) := by omega
      _ = (c.val + 1) * (N - 1) := by ring
      _ ≤ r * (N - 1) := Nat.mul_le_mul_right _ hc⟩

def g63d_blk {K N r : ℕ} {hK0 : 0 < K} {hN0 : 0 < N}
    (w : Messages (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1))) (c : Fin r) :
    BinaryArray K N := fun j i => w j ⟨(g63d_idx c i).val, by
      simpa [equalParameters] using (g63d_idx (N := N) c i).isLt⟩

abbrev g63d_m (K N : ℕ) (hK0 : 0 < K) (hN0 : 0 < N) : SpirParameters :=
  equalParameters 2 Nat.prime_two K N hK0 hN0

theorem g63d_bnd {N : ℕ} (hN : 2 ≤ N) (t : ℕ) : t % (N - 1) + 1 < N := by
  have := Nat.mod_lt t (show N - 1 > 0 by omega); omega

def g63d_ans {K N r : ℕ} {hK0 : 0 < K} {hN0 : 0 < N} (q : ℕ)
    (w : Messages (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1))) (s : ℕ) :
    List (ZMod 2) := List.ofFn (fun c : Fin r =>
    binaryAnswer (g63d_dec q : BinaryArray K N) (g63d_blk w c) ((g63d_dec s : Fin r → ZMod 2) c))

def g63d_decode {N L : ℕ} (hN0 : 0 < N) (hN : 2 ≤ N) (ans : Fin N → List (ZMod 2)) :
    Fin L → ZMod 2 := fun t =>
    (ans ⟨t.val % (N - 1) + 1, g63d_bnd hN t.val⟩).getD (t.val / (N - 1)) 0 -
      (ans ⟨0, hN0⟩).getD (t.val / (N - 1)) 0

def g63d_q {K N : ℕ} (k : Fin K) (h : ℕ) (n : Fin N) : ℕ :=
  g63d_enc (binaryQuery k n (g63d_dec h : BinaryArray K N))

def g63d_proto (K N r : ℕ) (hK0 : 0 < K) (hN0 : 0 < N) (hN : 2 ≤ N) (hr : 0 < r) :
    SpirProtocol (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) where
  length_pos := Nat.mul_pos hr (by omega)
  userSeed := (PMF.uniformOfFintype (BinaryArray K N)).map g63d_enc
  sharedSeed := (PMF.uniformOfFintype (Fin r → ZMod 2)).map g63d_enc
  query := fun k h n => g63d_q (K := K) (N := N) k h n
  format := fun _ _ => r
  answer := fun _ q w s => g63d_ans q w s
  answer_length := by intros; exact List.length_ofFn
  decode := fun _ _ _ ans => g63d_decode hN0 hN ans
  download := r * N
  download_bound := by intros; show (∑ _n : Fin N, r) ≤ r * N; simp [mul_comm]
  download_attained := ⟨⟨0, hK0⟩, g63d_enc (0 : BinaryArray K N), by
    rw [← PMF.mem_support_iff, PMF.mem_support_map_iff]
    exact ⟨0, PMF.mem_support_uniformOfFintype _, rfl⟩, by show (∑ _n : Fin N, r) = r * N; simp [mul_comm]⟩

theorem g63d_unif3 {A B C : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype C] [Nonempty C] :
    (PMF.uniformOfFintype A).bind (fun w => (PMF.uniformOfFintype B).bind (fun h =>
      (PMF.uniformOfFintype C).map (fun s => (w, h, s)))) = PMF.uniformOfFintype (A × B × C) := by
  ext ⟨w0, h0, s0⟩
  simp only [PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply, Prod.mk.injEq]
  rw [tsum_eq_single w0, tsum_eq_single h0, tsum_eq_single s0]
  · simp only [and_self, if_true, Fintype.card_prod]
    push_cast
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
      ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  · intro s hs; simp [Ne.symm hs]
  · intro h hh; simp [Ne.symm hh]
  · intro w hw; simp [Ne.symm hw]

section
variable (K N r : ℕ) (hK0 : 0 < K) (hN0 : 0 < N) (hN : 2 ≤ N) (hr : 0 < r)

abbrev g63d_Om := Messages (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) ×
  BinaryArray K N × (Fin r → ZMod 2)

def g63d_E (x : g63d_Om K N r hK0 hN0) :
    Messages (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) × ℕ × ℕ :=
  (x.1, g63d_enc x.2.1, g63d_enc x.2.2)

theorem g63d_dl : dataLaw (g63d_proto K N r hK0 hN0 hN hr) =
    (PMF.uniformOfFintype (g63d_Om K N r hK0 hN0)).map (g63d_E K N r hK0 hN0) := by
  rw [← g63d_unif3]
  unfold dataLaw
  simp only [g63d_proto, PMF.bind_map, PMF.map_comp, PMF.map_bind]
  rfl

theorem g63d_query (k : Fin (equalParameters 2 Nat.prime_two K N hK0 hN0).K) (h : BinaryArray K N)
    (n : Fin (equalParameters 2 Nat.prime_two K N hK0 hN0).N) :
    (g63d_proto K N r hK0 hN0 hN hr).query k (g63d_enc h) n = g63d_enc (binaryQuery (N := N) k n h) := by
  show g63d_q (K := K) (N := N) k (g63d_enc h) n = _
  unfold g63d_q
  rw [g63d_dec_enc]
  exact rfl

theorem g63d_UP : UserPrivate (g63d_proto K N r hK0 hN0 hN hr) := by
  intro k k2 n
  have : Nonempty (g63d_Om K N r hK0 hN0) := ⟨(0, 0, 0)⟩
  set P := g63d_proto K N r hK0 hN0 hN hr
  let G : g63d_Om K N r hK0 hN0 → _ := fun x =>
    (g63d_enc x.2.1, P.answer n (g63d_enc x.2.1) x.1 (g63d_enc x.2.2), x.1, g63d_enc x.2.2)
  have key : ∀ k' : Fin (equalParameters 2 Nat.prime_two K N hK0 hN0).K,
      (dataLaw P).map (serverView P k' n) =
      (PMF.uniformOfFintype (g63d_Om K N r hK0 hN0)).map G := by
    intro k'
    let σ : g63d_Om K N r hK0 hN0 ≃ g63d_Om K N r hK0 hN0 := (Equiv.refl (Messages (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)))).prodCongr
      ((g63d_flip k' n).prodCongr (Equiv.refl (Fin r → ZMod 2)))
    have hc : serverView P k' n ∘ g63d_E K N r hK0 hN0 = G ∘ σ := by
      funext x
      obtain ⟨w, h, s⟩ := x
      show (P.query k' (g63d_enc h) n, P.answer n (P.query k' (g63d_enc h) n) w (g63d_enc s), w,
        g63d_enc s) = (g63d_enc (binaryQuery (N := N) k' n h),
          P.answer n (g63d_enc (binaryQuery (N := N) k' n h)) w (g63d_enc s), w, g63d_enc s)
      rw [g63d_query]
    rw [g63d_dl, PMF.map_comp, hc, ← PMF.map_comp, g63d_map_equiv]
  rw [key, key]

theorem g63d_getD {α : Type*} {r : ℕ} (f : Fin r → α) (c : ℕ) (hc : c < r) (d : α) :
    (List.ofFn f).getD c d = f ⟨c, hc⟩ := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem g63d_ZE : ZeroError (g63d_proto K N r hK0 hN0 hN hr) := by
  intro k
  set P := g63d_proto K N r hK0 hN0 hN hr
  unfold errorProbability
  have hF : (fun x => decide (P.decode k x.2.1 (P.query k x.2.1)
      (fun n => observedAnswer P k n x) ≠ x.1 k)) ∘ g63d_E K N r hK0 hN0 = fun _ => false := by
    funext x
    obtain ⟨w, h, s⟩ := x
    simp only [Function.comp_apply, g63d_E]
    apply decide_eq_false
    intro hne; apply hne
    funext t
    have hN1 : 0 < N - 1 := by omega
    have ht : t.val < 1 * (r * (N - 1)) := t.isLt
    have hc : t.val / (N - 1) < r := by
      rw [Nat.div_lt_iff_lt_mul hN1]; omega
    show g63d_decode hN0 hN (fun n => g63d_ans (g63d_q (K := K) (N := N) k (g63d_enc h) n)
      w (g63d_enc s)) t = w k t
    simp only [g63d_decode, g63d_ans, g63d_q, g63d_dec_enc, g63d_getD _ _ hc]
    have := g63d_bin_c1 K N hN k (g63d_blk w ⟨t.val / (N - 1), hc⟩) h (s ⟨t.val / (N - 1), hc⟩)
      ⟨t.val % (N - 1), Nat.mod_lt _ hN1⟩
    refine this.trans ?_
    simp only [g63d_blk, g63d_idx]
    congr 1
    exact Fin.ext (Nat.div_add_mod' t.val (N - 1))
  rw [g63d_dl, PMF.map_comp, hF]
  have : (fun _ : g63d_Om K N r hK0 hN0 => false) = Function.const _ false := rfl
  rw [this, PMF.map_const]
  simp

def g63d_tau (k : Fin (equalParameters 2 Nat.prime_two K N hK0 hN0).K) : g63d_Om K N r hK0 hN0 ≃
    (((j : {j // j ≠ k}) → Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) j.val) ×
      (Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) k ×
        BinaryArray K N × (Fin r → ZMod 2))) where
  toFun x := ((Equiv.piSplitAt k _ x.1).2, (x.1 k, x.2.1,
    x.2.2 + fun c => binaryAnswer x.2.1 (g63d_blk x.1 c) 0))
  invFun y := ((Equiv.piSplitAt k _).symm (y.2.1, y.1), y.2.2.1,
    y.2.2.2 - fun c => binaryAnswer y.2.2.1 (g63d_blk ((Equiv.piSplitAt k _).symm (y.2.1, y.1)) c) 0)
  left_inv x := by
    obtain ⟨w, h, s⟩ := x
    have : (Equiv.piSplitAt k _).symm (w k, (Equiv.piSplitAt k _ w).2) = w :=
      (Equiv.piSplitAt k (fun j => Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) j)).symm_apply_apply w
    simp only [this, add_sub_cancel_right]
  right_inv y := by
    obtain ⟨u, a, h, s⟩ := y
    have := (Equiv.piSplitAt k (fun j => Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) j)).apply_symm_apply (a, u)
    simp only [Prod.ext_iff] at this
    have h1 : (Equiv.piSplitAt k (fun j => Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) j)).symm (a, u) k = a := this.1
    have h2 := this.2
    simp only [h1, h2, sub_add_cancel]

def g63d_uans (k : Fin (equalParameters 2 Nat.prime_two K N hK0 hN0).K) (n : Fin N)
    (wk : Message (equalParameters 2 Nat.prime_two K N hK0 hN0) (r * (N - 1)) k)
    (s' : Fin r → ZMod 2) : List (ZMod 2) :=
  List.ofFn (fun c : Fin r => s' c + g63d_e n (fun i => wk ⟨(g63d_idx c i).val, by
      simpa [equalParameters] using (g63d_idx (N := N) c i).isLt⟩))

theorem g63d_DP : DatabasePrivate (g63d_proto K N r hK0 hN0 hN hr) := by
  intro k
  have : Nonempty (g63d_Om K N r hK0 hN0) := ⟨(0, 0, 0)⟩
  set P := g63d_proto K N r hK0 hN0 hN hr
  rw [g63d_dl, g63d_indep_map]
  refine g63d_indep_equiv (g63d_tau K N r hK0 hN0 k) _ _ (fun u => u)
    (fun y => ((fun n : Fin N => g63d_enc (binaryQuery k n y.2.1)),
      (fun n => (g63d_uans K N r hK0 hN0 k n y.1 y.2.2 : List (ZMod (equalParameters 2 Nat.prime_two K N hK0 hN0).p))),
      g63d_enc y.2.1)) (fun x => rfl) (fun x => ?_)
  obtain ⟨w, h, s⟩ := x
  simp only [Function.comp_apply, userView, g63d_E, g63d_tau, Equiv.coe_fn_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext n; exact g63d_query K N r hK0 hN0 hN hr k h n
  · funext n
    show g63d_ans (g63d_q (K := K) (N := N) k (g63d_enc h) n) w (g63d_enc s) =
      g63d_uans K N r hK0 hN0 k n (w k) (s + fun c => binaryAnswer h (g63d_blk w c) 0)
    simp only [g63d_ans, g63d_uans, g63d_q, g63d_dec_enc]
    congr 1
    funext c
    refine (g63d_ans_flip (K := K) (N := N) k n h _ _).trans ?_
    show binaryAnswer h (g63d_blk w c) (s c) + g63d_e n (g63d_blk w c k) =
      (s c + binaryAnswer h (g63d_blk w c) 0) + g63d_e n (g63d_blk w c k)
    unfold binaryAnswer
    ring
  · rfl

end

theorem solution (K N : ℕ) (hK : 2 ≤ K) (hN : 2 ≤ N) :
    (∀ (k : Fin K) (w h : BinaryArray K N) (s : ZMod 2) (i : Fin (N - 1)),
      binaryAnswer (binaryQuery k (⟨i.val + 1, by omega⟩ : Fin N) h) w s -
        binaryAnswer (binaryQuery k (⟨0, by omega⟩ : Fin N) h) w s = w k i) ∧
    (∀ (k k2 : Fin K) (n : Fin N),
      (spirBinaryLaw K N).map (binaryServerView k n) =
        (spirBinaryLaw K N).map (binaryServerView k2 n)) ∧
    (∀ k : Fin K, Independent (spirBinaryLaw K N) (binaryUndesired k) (binaryUserView k)) ∧
    binaryDownload N = N ∧
    spirEntropy 2 (PMF.uniformOfFintype (ZMod 2)) = 1 ∧
    ((N - 1 : ℕ) : ℝ) / (binaryDownload N : ℝ) = 1 - 1 / (N : ℝ) ∧
    spirEntropy 2 (PMF.uniformOfFintype (ZMod 2)) / ((N - 1 : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (1 / ((N : ℝ) - 1)) ∧
    (∀ r : ℕ, 0 < r →
      ∃ b : SpirProtocol
        (equalParameters 2 Nat.prime_two K N (by omega) (by omega)) (r * (N - 1)),
        Private b ∧ ZeroError b ∧ b.download = r * N ∧
          spirEntropy 2 b.sharedSeed = (r : ℝ≥0∞) ∧
          ∀ k, spirRate b k = 1 - 1 / (N : ℝ)) := by
  have hent : spirEntropy 2 (PMF.uniformOfFintype (ZMod 2)) = 1 := by
    rw [g63d_ent_unif]
    simp
    norm_num
  refine ⟨fun k w h s i => g63d_bin_c1 K N hN k w h s i, fun k k2 n => g63d_bin_c2 K N hK hN k k2 n,
    fun k => g63d_bin_c3 K N hK hN k, by simp [binaryDownload], hent, ?_, ?_, ?_⟩
  · have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [show binaryDownload N = N by simp [binaryDownload]]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    field_simp
    push_cast
    ring
  · rw [hent]
    have h1 : ((N : ℝ) - 1) = ((N - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring
    have h2 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
    rw [h1, ENNReal.ofReal_div_of_pos h2, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  · intro r hr
    refine ⟨g63d_proto K N r (by omega) (by omega) hN hr,
      ⟨g63d_UP K N r _ _ hN hr, g63d_DP K N r _ _ hN hr⟩, g63d_ZE K N r _ _ hN hr, rfl, ?_, ?_⟩
    · show spirEntropy 2 ((PMF.uniformOfFintype (Fin r → ZMod 2)).map g63d_enc) = _
      rw [g63d_ent_unif_map 2 _ g63d_enc_inj]
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      push_cast
      rw [Real.log_pow]
      have : Real.log 2 ≠ 0 := by positivity
      field_simp
      simp
    · intro k
      unfold spirRate
      show (((1 * (r * (N - 1)) : ℕ) : ℝ)) / (((r * N : ℕ) : ℝ)) = 1 - 1 / (N : ℝ)
      have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N)]
      field_simp
      push_cast
      ring
