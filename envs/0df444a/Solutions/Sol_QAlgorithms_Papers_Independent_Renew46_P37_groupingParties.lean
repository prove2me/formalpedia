-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.groupingParties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:51:10.520553+00:00
-- url     : https://prove2.me/submissions/665dfe80-5a37-4680-a4b7-d69663b17fe0

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P37

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

section psv204_gp
variable {m n : ℕ} (g : Fin m → Fin n)

abbrev psv204_B (d : Fin m → ℕ) (b : Fin n) : Type :=
  (i : {i : Fin m // g i = b}) → Fin (d i.val)

def psv204_D (d : Fin m → ℕ) : Fin n → ℕ := fun b => Fintype.card (psv204_B g d b)

def psv204_E (d : Fin m → ℕ) (b : Fin n) : psv204_B g d b ≃ Fin (psv204_D g d b) :=
  Fintype.equivFin _

def psv204_Phi (d : Fin m → ℕ) (x : ClassicalBasis d) : ClassicalBasis (psv204_D g d) :=
  fun b => psv204_E g d b (fun i => x i.val)

def psv204_Psi (d : Fin m → ℕ) (y : ClassicalBasis (psv204_D g d)) : ClassicalBasis d :=
  fun i => (psv204_E g d (g i)).symm (y (g i)) ⟨i, rfl⟩

lemma psv204_fiber (d : Fin m → ℕ) (y : ClassicalBasis (psv204_D g d)) (b : Fin n)
    (i : {i : Fin m // g i = b}) :
    (psv204_E g d (g i.val)).symm (y (g i.val)) ⟨i.val, rfl⟩ = (psv204_E g d b).symm (y b) i := by
  obtain ⟨_, hi⟩ := i; subst hi; rfl

lemma psv204_Psi_Phi (d : Fin m → ℕ) (x : ClassicalBasis d) :
    psv204_Psi g d (psv204_Phi g d x) = x := by
  funext i; simp [psv204_Psi, psv204_Phi]

lemma psv204_Phi_Psi (d : Fin m → ℕ) (y : ClassicalBasis (psv204_D g d)) :
    psv204_Phi g d (psv204_Psi g d y) = y := by
  funext b
  simp only [psv204_Phi, psv204_Psi]
  rw [show (fun i : {i // g i = b} => (psv204_E g d (g i.val)).symm (y (g i.val)) ⟨i.val, rfl⟩)
    = (psv204_E g d b).symm (y b) from funext (psv204_fiber g d y b)]
  simp

def psv204_Eq (d : Fin m → ℕ) : ClassicalBasis d ≃ ClassicalBasis (psv204_D g d) :=
  ⟨psv204_Phi g d, psv204_Psi g d, psv204_Psi_Phi g d, psv204_Phi_Psi g d⟩

lemma psv204_Eq_apply (d : Fin m → ℕ) (x : ClassicalBasis d) :
    psv204_Eq g d x = psv204_Phi g d x := rfl

lemma psv204_gd_dims (p : CData m) : (groupData g p).dims = psv204_D g p.dims := rfl

lemma psv204_gd_prob (p : CData m) (y : ClassicalBasis (psv204_D g p.dims)) :
    (groupData g p).prob y = p.prob (psv204_Psi g p.dims y) := by
  show (∑ x : ClassicalBasis p.dims, if ∀ b, y b = psv204_Phi g p.dims x b then p.prob x else 0) = _
  rw [Finset.sum_eq_single (psv204_Psi g p.dims y)]
  · rw [if_pos (fun b => by rw [psv204_Phi_Psi])]
  · intro x _ hx
    rw [if_neg]
    intro h
    apply hx
    rw [show y = psv204_Phi g p.dims x from funext h, psv204_Psi_Phi]
  · simp

lemma psv204_gd_prob' (p : CData m) (x : ClassicalBasis p.dims) :
    (groupData g p).prob (psv204_Phi g p.dims x) = p.prob x := by
  rw [psv204_gd_prob, psv204_Psi_Phi]

lemma psv204_D_pos (d : Fin m → ℕ) (hd : ∀ i, 0 < d i) (b : Fin n) : 0 < psv204_D g d b :=
  Fintype.card_pos_iff.mpr ⟨fun i => ⟨0, hd _⟩⟩

lemma psv204_gd_valid (p : CData m) (hp : IsValidClassicalData p) :
    IsValidClassicalData (groupData g p) := by
  refine ⟨psv204_D_pos g _ hp.1, fun y => ?_, ?_⟩
  · exact le_of_le_of_eq (hp.2.1 _) (psv204_gd_prob g p y).symm
  · show ∑ y : ClassicalBasis (psv204_D g p.dims), (groupData g p).prob y = 1
    rw [Finset.sum_congr rfl (fun y _ => psv204_gd_prob g p y)]
    exact (Equiv.sum_comp (psv204_Eq g p.dims).symm p.prob).trans hp.2.2

lemma psv204_gd_indep (p : CData m) (hp : IsIndependentLaw p) :
    IsIndependentLaw (groupData g p) := by
  obtain ⟨q, hq, hx⟩ := hp
  refine ⟨fun b Y => ∏ i : {i // g i = b}, q i.val ((psv204_E g p.dims b).symm Y i),
    fun b => ⟨fun Y => Finset.prod_nonneg (fun i _ => (hq _).1 _), ?_⟩, fun y => ?_⟩
  · show ∑ Y, ∏ i : {i // g i = b}, q i.val ((psv204_E g p.dims b).symm Y i) = 1
    rw [Equiv.sum_comp (psv204_E g p.dims b).symm
      (fun F => ∏ i : {i // g i = b}, q i.val (F i)), ← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun i _ => (hq _).2)
  · refine (psv204_gd_prob g p y).trans ?_
    rw [hx, ← Fintype.prod_fiberwise g]
    refine Finset.prod_congr rfl (fun b _ => Finset.prod_congr rfl (fun i _ => ?_))
    exact congrArg (q i.val) (psv204_fiber g p.dims y b i)

lemma psv204_codeval {S : Type} [Fintype S] [DecidableEq S] (δ δ' : S → ℕ) (h : δ = δ')
    (u : (i : S) → Fin (δ i)) (v : (i : S) → Fin (δ' i)) :
    (Fintype.equivFin ((i : S) → Fin (δ i)) u).val =
      (Fintype.equivFin ((i : S) → Fin (δ' i)) v).val ↔ ∀ i, (u i).val = (v i).val := by
  subst h
  constructor
  · intro hv i
    rw [(Fintype.equivFin _).injective (Fin.ext hv)]
  · intro hv
    rw [show u = v from funext fun i => Fin.ext (hv i)]

lemma psv204_Ecode (d d' : Fin m → ℕ) (b : Fin n) (h : ∀ i, g i = b → d i = d' i)
    (u : psv204_B g d b) (v : psv204_B g d' b) :
    (psv204_E g d b u).val = (psv204_E g d' b v).val ↔ ∀ i, (u i).val = (v i).val :=
  psv204_codeval (fun i : {i // g i = b} => d i.val) (fun i => d' i.val)
    (funext fun i => h i.val i.2) u v

lemma psv204_sum_slot {S : Type} [Fintype S] [DecidableEq S] (d d' : S → ℕ) (s0 : S)
    (hd : ∀ i, i ≠ s0 → d' i = d i) (u : (i : S) → Fin (d i)) (φ : Fin (d' s0) → ℝ) :
    ∑ F : (i : S) → Fin (d' i),
      φ (F s0) * (if ∀ i, i ≠ s0 → (u i).val = (F i).val then 1 else 0) = ∑ c, φ c := by
  let Fc : Fin (d' s0) → (i : S) → Fin (d' i) := fun c i =>
    if h : i = s0 then ⟨c.val, by subst h; exact c.isLt⟩
    else ⟨(u i).val, by rw [hd i h]; exact (u i).isLt⟩
  have hFc : ∀ c, Fc c s0 = c := fun c => Fin.ext (by simp [Fc])
  symm
  refine Fintype.sum_of_injective Fc (fun c c' h => by rw [← hFc c, ← hFc c', h]) _ _ ?_ ?_
  · intro F hF
    rw [if_neg, mul_zero]
    intro hc
    apply hF
    refine ⟨F s0, funext fun i => ?_⟩
    by_cases hi : i = s0
    · subst hi; exact hFc _
    · exact Fin.ext (by simp [Fc, hi, hc i hi])
  · intro c
    rw [hFc, if_pos, mul_one]
    intro i hi
    simp [Fc, hi]

lemma psv204_gd_inst (p : CData m) (k : ℕ) (w : Fin k → ℝ) (r : Fin k → CData m)
    (h : CInstrument p w r) : CInstrument (groupData g p) w (fun j => groupData g (r j)) := by
  obtain ⟨hp, hw, hr, a, K, hdim, hK0, hK1, hEq⟩ := h
  let s0 : {i // g i = g a} := ⟨a, rfl⟩
  refine ⟨psv204_gd_valid g p hp, hw, fun j => psv204_gd_valid g _ (hr j), g a,
    fun j A B => K j ((psv204_E g p.dims (g a)).symm A s0)
      ((psv204_E g (r j).dims (g a)).symm B s0) *
      (if ∀ i, i ≠ s0 → ((psv204_E g p.dims (g a)).symm A i).val =
        ((psv204_E g (r j).dims (g a)).symm B i).val then 1 else 0), ?_, ?_, ?_, ?_⟩
  · intro j b hb
    show psv204_D g (r j).dims b = psv204_D g p.dims b
    simp only [psv204_D, psv204_B, Fintype.card_pi, Fintype.card_fin]
    exact Finset.prod_congr rfl (fun i _ => hdim j i.val (fun h => hb (by rw [← i.2, h])))
  · intro j A B
    exact mul_nonneg (hK0 _ _ _) (by split_ifs <;> norm_num)
  · intro A
    change Fin (psv204_D g p.dims (g a)) at A
    refine Eq.trans ?_ (hK1 ((psv204_E g p.dims (g a)).symm A s0))
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (Equiv.sum_comp (psv204_E g (r j).dims (g a)) _).symm.trans ?_
    simp only [Equiv.symm_apply_apply]
    exact psv204_sum_slot (fun i : {i // g i = g a} => p.dims i.val)
      (fun i => (r j).dims i.val) s0
      (fun i hi => hdim j i.val (fun h => hi (Subtype.ext h))) _ (K j _)
  · intro j Y
    change ClassicalBasis (psv204_D g (r j).dims) at Y
    obtain ⟨y, rfl⟩ := (psv204_Eq g (r j).dims).surjective Y
    change w j * (groupData g (r j)).prob (psv204_Phi g (r j).dims y) = _
    rw [psv204_gd_prob', hEq j y]
    refine Eq.trans ?_ (Equiv.sum_comp (psv204_Eq g p.dims) _)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    change _ = if ∀ b, b ≠ g a → (psv204_Phi g p.dims x b).val = (psv204_Phi g (r j).dims y b).val
      then (groupData g p).prob (psv204_Phi g p.dims x) * _ else 0
    rw [psv204_gd_prob']
    simp only [psv204_Eq_apply, psv204_Phi, Equiv.symm_apply_apply]
    have hC1 : ∀ b, b ≠ g a → ((psv204_E g p.dims b (fun i => x i.val)).val =
        (psv204_E g (r j).dims b (fun i => y i.val)).val ↔
        ∀ i : {i // g i = b}, (x i.val).val = (y i.val).val) := by
      intro b hb
      exact psv204_Ecode g p.dims (r j).dims b
        (fun i hi => (hdim j i (fun h => hb (by rw [← hi, h]))).symm) _ _
    have key : (∀ i, i ≠ a → (x i).val = (y i).val) ↔
        (∀ b, b ≠ g a → ∀ i : {i // g i = b}, (x i.val).val = (y i.val).val) ∧
        (∀ i : {i // g i = g a}, i ≠ s0 → (x i.val).val = (y i.val).val) := by
      constructor
      · intro hc
        refine ⟨fun b hb i => hc i.val (fun h => hb (by rw [← i.2, h])),
          fun i hi => hc i.val (fun h => hi (Subtype.ext h))⟩
      · rintro ⟨h1, h2⟩ i hi
        by_cases hgi : g i = g a
        · exact h2 ⟨i, hgi⟩ (fun h => hi (congrArg Subtype.val h))
        · exact h1 (g i) hgi ⟨i, rfl⟩
    by_cases hC : ∀ i, i ≠ a → (x i).val = (y i).val
    · obtain ⟨h1, h2⟩ := key.1 hC
      rw [if_pos hC]
      split_ifs with H1
      · rw [mul_one]
      · exact absurd (fun b hb => (hC1 b hb).2 (h1 b hb)) H1
    · rw [if_neg hC]
      split_ifs with H1 H2
      · exact absurd (key.2 ⟨fun b hb => (hC1 b hb).1 (H1 b hb), H2⟩) hC
      · rw [mul_zero, mul_zero]
      · rfl

end psv204_gp
section psv204_rel
variable {n : ℕ} (M : CData n → ℝ) (hM : IsCMonotone M)
include hM

lemma psv204_RL1 (s t : CData n) (hs : IsValidClassicalData s) (ht : IsValidClassicalData t)
    (a : Fin n) (hd : ∀ i, i ≠ a → t.dims i = s.dims i) (τ : Fin (s.dims a) ≃ Fin (t.dims a))
    (hc : ∀ x y, (∀ i, i ≠ a → (x i).val = (y i).val) → τ (x a) = y a → t.prob y = s.prob x) :
    M t ≤ M s := by
  have hI : CInstrument s (fun _ : Fin 1 => (1 : ℝ)) (fun _ => t) := by
    refine ⟨hs, ⟨fun _ => zero_le_one, by simp⟩, fun _ => ht, a,
      fun _ u v => if τ u = v then 1 else 0, fun _ i hi => hd i hi,
      fun _ u v => by dsimp only; split_ifs <;> norm_num, fun u => by simp, fun _ y => ?_⟩
    beta_reduce
    let x0 : ClassicalBasis s.dims := fun i =>
      if h : i = a then ⟨(τ.symm (y a)).val, by rw [h]; exact (τ.symm (y a)).isLt⟩
      else ⟨(y i).val, by rw [← hd i h]; exact (y i).isLt⟩
    have hx0a : x0 a = τ.symm (y a) := Fin.ext (by simp [x0])
    have hx0 : ∀ i, i ≠ a → (x0 i).val = (y i).val := fun i hi => by simp [x0, hi]
    rw [Finset.sum_eq_single x0, if_pos hx0, hx0a, Equiv.apply_symm_apply, if_pos rfl, mul_one,
      one_mul]
    · exact hc x0 y hx0 (by rw [hx0a, Equiv.apply_symm_apply])
    · intro x _ hx
      by_cases hc1 : ∀ i, i ≠ a → (x i).val = (y i).val
      · rw [if_pos hc1]
        by_cases hc2 : τ (x a) = y a
        · exfalso; apply hx
          funext i
          by_cases hi : i = a
          · subst hi; rw [hx0a, ← hc2, Equiv.symm_apply_apply]
          · exact Fin.ext ((hc1 i hi).trans (hx0 i hi).symm)
        · rw [if_neg hc2, mul_zero]
      · rw [if_neg hc1]
    · simp
  have := hM.2.2.1 s 1 _ _ hI
  simpa using this

lemma psv204_RLeq (s t : CData n) (hs : IsValidClassicalData s) (ht : IsValidClassicalData t)
    (a : Fin n) (hd : ∀ i, i ≠ a → t.dims i = s.dims i) (τ : Fin (s.dims a) ≃ Fin (t.dims a))
    (hc : ∀ x y, (∀ i, i ≠ a → (x i).val = (y i).val) → τ (x a) = y a → t.prob y = s.prob x) :
    M s = M t := by
  refine le_antisymm ?_ (psv204_RL1 M hM s t hs ht a hd τ hc)
  refine psv204_RL1 M hM t s ht hs a (fun i hi => (hd i hi).symm) τ.symm ?_
  intro x y h1 h2
  exact (hc y x (fun i hi => (h1 i hi).symm) (by rw [← h2, Equiv.apply_symm_apply])).symm

omit hM in
lemma psv204_valid_of (s t : CData n) (hs : IsValidClassicalData s)
    (ε : ∀ i, Fin (t.dims i) ≃ Fin (s.dims i))
    (hp : ∀ y, t.prob y = s.prob (fun i => ε i (y i))) : IsValidClassicalData t := by
  refine ⟨fun i => ?_, fun y => (hp y).symm ▸ hs.2.1 _, ?_⟩
  · have := Fintype.card_congr (ε i); simp only [Fintype.card_fin] at this
    rw [this]; exact hs.1 i
  · rw [Finset.sum_congr rfl (fun y _ => hp y)]
    exact (Equiv.sum_comp (Equiv.piCongrRight ε) s.prob).trans hs.2.2

end psv204_rel

section psv204_chain
variable {n : ℕ}

def psv204_md (s t : CData n) (k : ℕ) : Fin n → ℕ := fun i => if i.val < k then t.dims i else s.dims i

def psv204_me (s t : CData n) (σ : ∀ i, Fin (s.dims i) ≃ Fin (t.dims i)) (k : ℕ) (i : Fin n) :
    Fin (psv204_md s t k i) ≃ Fin (s.dims i) :=
  if h : i.val < k then (finCongr (by simp [psv204_md, h])).trans (σ i).symm
  else finCongr (by simp [psv204_md, h])

def psv204_mid (s t : CData n) (σ : ∀ i, Fin (s.dims i) ≃ Fin (t.dims i)) (k : ℕ) : CData n :=
  ⟨psv204_md s t k, fun x => s.prob (fun i => psv204_me s t σ k i (x i))⟩

lemma psv204_me_lt (s t : CData n) (σ : ∀ i, Fin (s.dims i) ≃ Fin (t.dims i)) (k : ℕ)
    (i : Fin n) (h : i.val < k) (z : Fin (psv204_md s t k i)) :
    psv204_me s t σ k i z = (σ i).symm ⟨z.val, by simpa [psv204_md, h] using z.isLt⟩ := by
  rw [psv204_me, dif_pos h]; rfl

lemma psv204_me_ge (s t : CData n) (σ : ∀ i, Fin (s.dims i) ≃ Fin (t.dims i)) (k : ℕ)
    (i : Fin n) (h : ¬ i.val < k) (z : Fin (psv204_md s t k i)) :
    (psv204_me s t σ k i z).val = z.val := by
  rw [psv204_me, dif_neg h]; rfl

lemma psv204_RL (M : CData n → ℝ) (hM : IsCMonotone M) (hn : 0 < n) (s t : CData n)
    (hs : IsValidClassicalData s) (σ : ∀ i, Fin (s.dims i) ≃ Fin (t.dims i))
    (hp : ∀ x, t.prob (fun i => σ i (x i)) = s.prob x) : M s = M t := by
  have ht : IsValidClassicalData t := psv204_valid_of s t hs (fun i => (σ i).symm)
    (fun y => by rw [← hp]; simp)
  have hv : ∀ k, IsValidClassicalData (psv204_mid s t σ k) := fun k =>
    psv204_valid_of s _ hs (fun i => psv204_me s t σ k i) (fun y => rfl)
  let a0 : Fin n := ⟨0, hn⟩
  have h0 : M s = M (psv204_mid s t σ 0) := by
    refine psv204_RLeq M hM s _ hs (hv 0) a0 (fun i _ => by simp [psv204_mid, psv204_md])
      (psv204_me s t σ 0 a0).symm ?_
    intro x y h1 h2
    show s.prob (fun i => psv204_me s t σ 0 i (y i)) = s.prob x
    congr 1; funext i
    by_cases hi : i = a0
    · subst hi; rw [← h2]; exact Equiv.apply_symm_apply _ _
    · exact Fin.ext ((psv204_me_ge s t σ 0 i (Nat.not_lt_zero _) _).trans (h1 i hi).symm)
  have hstep : ∀ k, k < n → M (psv204_mid s t σ k) = M (psv204_mid s t σ (k + 1)) := by
    intro k hk
    let a : Fin n := ⟨k, hk⟩
    refine psv204_RLeq M hM _ _ (hv k) (hv (k + 1)) a ?_
      ((psv204_me s t σ k a).trans (psv204_me s t σ (k + 1) a).symm) ?_
    · intro i hi
      have : i.val ≠ k := fun h => hi (Fin.ext h)
      show psv204_md s t (k + 1) i = psv204_md s t k i
      by_cases h1 : i.val < k <;> by_cases h2 : i.val < k + 1 <;> simp [psv204_md, h1, h2] <;>
        omega
    · intro x y h1 h2
      show s.prob (fun i => psv204_me s t σ (k + 1) i (y i)) =
        s.prob (fun i => psv204_me s t σ k i (x i))
      congr 1; funext i
      by_cases hi : i = a
      · subst hi; rw [← h2]; exact Equiv.apply_symm_apply _ _
      · have hvv := h1 i hi
        have hik : i.val ≠ k := fun h => hi (Fin.ext h)
        by_cases hlt : i.val < k
        · refine (psv204_me_lt s t σ (k + 1) i (by omega) (y i)).trans
            (Eq.trans ?_ (psv204_me_lt s t σ k i hlt (x i)).symm)
          congr 1; exact Fin.ext hvv.symm
        · exact Fin.ext ((psv204_me_ge s t σ (k + 1) i (by omega) _).trans
            (hvv.symm.trans (psv204_me_ge s t σ k i hlt _).symm))
  have hend : M (psv204_mid s t σ n) = M t := by
    refine psv204_RLeq M hM _ t (hv n) ht a0 (fun i _ => by simp [psv204_mid, psv204_md, i.isLt])
      ((psv204_me s t σ n a0).trans (σ a0)) ?_
    intro x y h1 h2
    show t.prob y = s.prob (fun i => psv204_me s t σ n i (x i))
    rw [← hp]
    congr 1; funext i
    by_cases hi : i = a0
    · subst hi; exact h2.symm
    · refine Eq.trans ?_ (congrArg (σ i) (psv204_me_lt s t σ n i i.isLt (x i))).symm
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (h1 i hi).symm
  have chain : ∀ k, k ≤ n → M s = M (psv204_mid s t σ k) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih => intro hk; rw [ih (by omega)]; exact hstep k (by omega)
  exact (chain n le_rfl).trans hend

end psv204_chain

def psv204_split {S : Type} (d1 d2 : S → ℕ) :
    ((i : S) → Fin (d1 i * d2 i)) ≃ ((i : S) → Fin (d1 i)) × ((i : S) → Fin (d2 i)) where
  toFun F := (fun i => (finProdFinEquiv.symm (F i)).1, fun i => (finProdFinEquiv.symm (F i)).2)
  invFun z i := finProdFinEquiv (z.1 i, z.2 i)
  left_inv F := by funext i; exact finProdFinEquiv.apply_symm_apply (F i)
  right_inv z := by ext i <;> simp

lemma psv204_cp_valid {n : ℕ} (p q : CData n) (hp : IsValidClassicalData p)
    (hq : IsValidClassicalData q) : IsValidClassicalData (cProduct p q) := by
  refine ⟨fun i => Nat.mul_pos (hp.1 i) (hq.1 i), fun x => mul_nonneg (hp.2.1 _) (hq.2.1 _), ?_⟩
  show ∑ x, (fun z : ClassicalBasis p.dims × ClassicalBasis q.dims => p.prob z.1 * q.prob z.2)
    (psv204_split p.dims q.dims x) = 1
  rw [Equiv.sum_comp (psv204_split p.dims q.dims) (fun z => p.prob z.1 * q.prob z.2),
    Fintype.sum_prod_type, ← Finset.sum_mul_sum, hp.2.2, hq.2.2, mul_one]

section psv204_fin
variable {m n : ℕ} (g : Fin m → Fin n)

lemma psv204_gd_add (hn : 0 < n) (M : CData n → ℝ) (hM : IsCMonotone M) (p q : CData m)
    (hp : IsValidClassicalData p) (hq : IsValidClassicalData q) :
    M (groupData g (cProduct p q)) = M (groupData g p) + M (groupData g q) := by
  rw [← hM.2.2.2.1 _ _ (psv204_gd_valid g p hp) (psv204_gd_valid g q hq)]
  let σ : ∀ b, Fin (psv204_D g (fun i => p.dims i * q.dims i) b) ≃
      Fin (psv204_D g p.dims b * psv204_D g q.dims b) := fun b =>
    (psv204_E g (fun i => p.dims i * q.dims i) b).symm.trans
      ((psv204_split (fun i : {i // g i = b} => p.dims i.val) (fun i => q.dims i.val)).trans
        (((psv204_E g p.dims b).prodCongr (psv204_E g q.dims b)).trans finProdFinEquiv))
  refine psv204_RL M hM hn _ _ (psv204_gd_valid g _ (psv204_cp_valid p q hp hq)) σ ?_
  intro x
  change ClassicalBasis (psv204_D g (fun i => p.dims i * q.dims i)) at x
  have e1 : (fun b => (finProdFinEquiv.symm (σ b (x b))).1) = psv204_Phi g p.dims
      (fun j => (finProdFinEquiv.symm (psv204_Psi g (fun i => p.dims i * q.dims i) x j)).1) := by
    funext b
    simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      Prod.map, psv204_Phi]
    congr 1; funext i
    exact congrArg (fun z => (finProdFinEquiv.symm z).1) (psv204_fiber g _ x b i).symm
  have e2 : (fun b => (finProdFinEquiv.symm (σ b (x b))).2) = psv204_Phi g q.dims
      (fun j => (finProdFinEquiv.symm (psv204_Psi g (fun i => p.dims i * q.dims i) x j)).2) := by
    funext b
    simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      Prod.map, psv204_Phi]
    congr 1; funext i
    exact congrArg (fun z => (finProdFinEquiv.symm z).2) (psv204_fiber g _ x b i).symm
  show (groupData g p).prob (fun b => (finProdFinEquiv.symm (σ b (x b))).1) *
    (groupData g q).prob (fun b => (finProdFinEquiv.symm (σ b (x b))).2) =
    (groupData g (cProduct p q)).prob x
  rw [e1, e2, psv204_gd_prob', psv204_gd_prob']
  exact (psv204_gd_prob g (cProduct p q) x).symm

lemma psv204_gd_cont (M : CData n → ℝ) (hM : IsCMonotone M) (d : Fin m → ℕ)
    (hd : ∀ i, 0 < d i) :
    Continuous (fun p : {p : ClassicalBasis d → ℝ // IsLaw p} => M (groupData g ⟨d, p.val⟩)) := by
  have hc := hM.2.2.2.2 (psv204_D g d) (psv204_D_pos g d hd)
  let φ : {p : ClassicalBasis d → ℝ // IsLaw p} →
      {q : ClassicalBasis (psv204_D g d) → ℝ // IsLaw q} := fun p =>
    ⟨fun y => p.val (psv204_Psi g d y),
      ⟨fun y => p.2.1 _, (Equiv.sum_comp (psv204_Eq g d).symm p.val).trans p.2.2⟩⟩
  have hφ : Continuous φ := by
    apply Continuous.subtype_mk
    exact continuous_pi fun y => (continuous_apply (psv204_Psi g d y)).comp continuous_subtype_val
  have heq : (fun p : {p : ClassicalBasis d → ℝ // IsLaw p} => M (groupData g ⟨d, p.val⟩)) =
      (fun q : {q : ClassicalBasis (psv204_D g d) → ℝ // IsLaw q} => M ⟨psv204_D g d, q.val⟩) ∘ φ := by
    funext p
    exact congrArg (fun f => M ⟨psv204_D g d, f⟩)
      (funext fun y => psv204_gd_prob g ⟨d, p.val⟩ y)
  rw [heq]; exact hc.comp hφ

end psv204_fin

end QAlgorithms.Papers.Independent.Renew46.P37

open QAlgorithms.Papers.Independent.Renew46.P37 in
theorem solution {m n : ℕ} (hn : 2 ≤ n) (hm : n < m)
    (g : Fin m → Fin n) (hg : Function.Surjective g) (M : CData n → ℝ)
    (hM : IsCMonotone M) : IsCMonotone (fun p => M (groupData g p)) :=
  ⟨fun p hp => hM.1 _ (psv204_gd_valid g p hp),
   fun p hp hi => hM.2.1 _ (psv204_gd_valid g p hp) (psv204_gd_indep g p hi),
   fun p k w r h => hM.2.2.1 _ k w _ (psv204_gd_inst g p k w r h),
   fun p q hp hq => psv204_gd_add g (by omega) M hM p q hp hq,
   fun d hd => psv204_gd_cont g M hM d hd⟩

