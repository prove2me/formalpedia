-- Prove2me | solution 1 for YoungConventions.AdaptivePlay.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:42:39.945178+00:00
-- url     : https://prove2.me/submissions/5033ef56-2bb9-4189-bf76-cc13afc5104b

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_WeaklyAcyclic
import Definitions.Def_YoungConventions_AdaptivePlay_LGamma
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention

open Filter Topology Classical


namespace YoungConventions.AdaptivePlay

section UCB
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

theorem ucb_sink_strict (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) (hs : IsSink u s) :
    IsStrictNash u s := by
  intro i y hy
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ
    (fun x : S i => u i (Function.update s i x)) Finset.univ_nonempty
  have hbr : IsBestReply u i s x := fun z => hx z (Finset.mem_univ _)
  by_cases hxs : x = s i
  · subst hxs
    apply hs (Function.update s i y)
    refine ⟨i, y, hy, ?_, rfl⟩
    intro z
    have := hbr z
    simp only [Function.update_eq_self] at this hlt
    linarith
  · exact hs _ ⟨i, x, hxs, hbr, rfl⟩

theorem ucb_path_of_rtg (u : ι → (∀ i, S i) → ℝ) (s s' : ∀ i, S i)
    (h : Relation.ReflTransGen (BestReplyEdge u) s s') (hs' : IsStrictNash u s') :
    ∃ n, IsPathToStrictNash u s n := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => s', rfl, hs', fun j => j.elim0⟩
  | @head a c hac _ ih =>
    obtain ⟨n, f, hf0, hfl, hfe⟩ := ih
    refine ⟨n+1, Fin.cons a f, rfl, ?_, ?_⟩
    · rw [← Fin.succ_last, Fin.cons_succ]; exact hfl
    · intro j
      cases j using Fin.cases with
      | zero => simpa [hf0] using hac
      | succ j =>
        have := hfe j
        simpa [← Fin.succ_castSucc] using this

theorem ucb_short (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u) (s : ∀ i, S i) :
    ∃ r ≤ LGamma u, IsPathToStrictNash u s r := by
  obtain ⟨s', hr, hsink⟩ := hu s
  have hne : {n | IsPathToStrictNash u s n}.Nonempty :=
    ucb_path_of_rtg u s s' hr (ucb_sink_strict u s' hsink)
  refine ⟨shortestPathLength u s, ?_, Nat.sInf_mem hne⟩
  unfold LGamma
  exact Finset.le_sup (f := shortestPathLength u) (Finset.mem_univ s)

/-- the path as a function on ℕ -/
theorem ucb_short_nat (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u) (s : ∀ i, S i) :
    ∃ r ≤ LGamma u, ∃ g : ℕ → ∀ i, S i, g 0 = s ∧ IsStrictNash u (g r) ∧
      (∀ j < r, BestReplyEdge u (g j) (g (j+1))) ∧ (∀ j, r ≤ j → g j = g r) := by
  obtain ⟨r, hr, f, hf0, hfl, hfe⟩ := ucb_short u hu s
  refine ⟨r, hr, fun j => f ⟨min j r, by omega⟩, ?_, ?_, ?_, ?_⟩
  · simpa using hf0
  · convert hfl using 2
    ext; simp
  · intro j hj
    have := hfe ⟨j, hj⟩
    have e1 : (⟨min j r, by omega⟩ : Fin (r+1)) = (⟨j, hj⟩ : Fin r).castSucc := by
      ext; simp; omega
    have e2 : (⟨min (j+1) r, by omega⟩ : Fin (r+1)) = (⟨j, hj⟩ : Fin r).succ := by
      ext; simp; omega
    simp only
    rw [e1, e2]; exact this
  · intro j hj
    simp only
    congr 2 <;> omega

noncomputable def ucbSeq {m : ℕ} (h : History S m) (T : ℕ → ∀ i, S i) (j : ℕ) : ∀ i, S i :=
  if hj : j < m then h ⟨j, hj⟩ else T (j - m)

def ucbABR (u : ι → (∀ i, S i) → ℝ) (w : ℕ → ∀ i, S i) (k a : ℕ) (i : ι) (x : S i) : Prop :=
  ∀ y : S i, ∑ j ∈ Finset.Ico a (a+k), u i (Function.update (w j) i y) ≤
    ∑ j ∈ Finset.Ico a (a+k), u i (Function.update (w j) i x)

theorem ucbABR_congr (u : ι → (∀ i, S i) → ℝ) (w w' : ℕ → ∀ i, S i) (k a : ℕ) (i : ι) (x : S i)
    (hw : ∀ j ∈ Finset.Ico a (a+k), w j = w' j) (hx : ucbABR u w k a i x) :
    ucbABR u w' k a i x := by
  intro y
  have := hx y
  have e : ∀ z : S i, ∑ j ∈ Finset.Ico a (a+k), u i (Function.update (w j) i z) =
      ∑ j ∈ Finset.Ico a (a+k), u i (Function.update (w' j) i z) :=
    fun z => Finset.sum_congr rfl (fun j hj => by rw [hw j hj])
  rwa [e, e] at this

theorem ucbABR_const (u : ι → (∀ i, S i) → ℝ) (w : ℕ → ∀ i, S i) (k a : ℕ) (i : ι) (x : S i)
    (c : ∀ i, S i) (hw : ∀ j ∈ Finset.Ico a (a+k), w j = c) (hx : IsBestReply u i c x) :
    ucbABR u w k a i x := by
  intro y
  apply Finset.sum_le_sum
  intro j hj
  rw [hw j hj]
  exact hx y

theorem ucb_sample (u : ι → (∀ i, S i) → ℝ) {m : ℕ} (w : ℕ → ∀ i, S i) (k a n : ℕ)
    (hn : n ≤ a) (ha : a + k ≤ n + m) (i : ι) (x : S i) (hx : ucbABR u w k a i x) :
    ∃ K : Finset (Fin m), K.card = k ∧
      IsSampleBestReply u (fun t : Fin m => w (t.val + n)) K i x := by
  have hlt : ∀ j ∈ Finset.Ico (a - n) (a - n + k), j < m := by
    intro j hj; simp only [Finset.mem_Ico] at hj; omega
  refine ⟨(Finset.Ico (a-n) (a-n+k)).attachFin hlt, by simp, ?_⟩
  have key : ∀ g : ℕ → ℝ, ∑ t ∈ (Finset.Ico (a-n) (a-n+k)).attachFin hlt, g (t.val + n)
      = ∑ j ∈ Finset.Ico a (a+k), g j := by
    intro g
    have : ∑ t ∈ (Finset.Ico (a-n) (a-n+k)).attachFin hlt, g (t.val + n)
        = ∑ j ∈ Finset.Ico (a-n) (a-n+k), g (j + n) := by
      apply Finset.sum_bij (fun t _ => t.val)
      · intro t ht; simpa using ht
      · intro t1 _ t2 _ h; exact Fin.ext h
      · intro b hb; exact ⟨⟨b, hlt b hb⟩, by simpa using hb, rfl⟩
      · intro t _; rfl
    rw [this, Finset.sum_Ico_add', show a - n + n = a by omega,
      show a - n + k + n = a + k by omega]
  intro y
  have e1 := key (fun j => u i (Function.update (w j) i y))
  have e2 := key (fun j => u i (Function.update (w j) i x))
  simp only at e1 e2 ⊢
  rw [e1, e2]
  exact hx y

theorem ucb_strict_br (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) (hs : IsStrictNash u s) (i : ι) :
    IsBestReply u i s (s i) := by
  intro y
  rw [Function.update_eq_self]
  by_cases hy : y = s i
  · rw [hy, Function.update_eq_self]
  · exact (hs i y hy).le

theorem ucb_P_nonneg {m : ℕ} [NeZero m] (p : ∀ i, History S m → S i → ℝ)
    (hp0 : ∀ i h x, 0 ≤ p i h x) (n : ℕ) (x y : History S m) :
    0 ≤ (adaptivePlay p ^ n) x y := by
  induction n generalizing y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro z _
    apply mul_nonneg (ih z)
    unfold adaptivePlay
    split_ifs
    · exact Finset.prod_nonneg (fun i _ => hp0 i _ _)
    · exact le_rfl

theorem ucb_chain {m : ℕ} [NeZero m] (p : ∀ i, History S m → S i → ℝ)
    (hp0 : ∀ i h x, 0 ≤ p i h x) (st : ℕ → History S m)
    (hstep : ∀ n, 0 < adaptivePlay p (st n) (st (n+1))) (n : ℕ) :
    0 < (adaptivePlay p ^ n) (st 0) (st n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    calc (0:ℝ) < (adaptivePlay p ^ n) (st 0) (st n) * adaptivePlay p (st n) (st (n+1)) :=
          mul_pos ih (hstep n)
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun z => (adaptivePlay p ^ n) (st 0) z *
          adaptivePlay p z (st (n+1))) _ (Finset.mem_univ _)
        intro z _
        apply mul_nonneg (ucb_P_nonneg p hp0 n _ _)
        simpa using ucb_P_nonneg p hp0 1 z (st (n+1))

theorem ucb_reach (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    ∃ s : ∀ i, S i, IsStrictNash u s ∧
      0 < (adaptivePlay p ^ (k * LGamma u + m)) h (fun _ => s) := by
  have hm : 0 < m := NeZero.pos m
  -- choose the initial best reply to η
  let s₀ : ∀ i, S i := fun i => Classical.arbitrary _
  let w0 : ℕ → ∀ i, S i := ucbSeq h (fun _ => s₀)
  have hex : ∀ i, ∃ x : S i, ucbABR u w0 k (m-k) i x := by
    intro i
    obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ
      (fun x : S i => ∑ j ∈ Finset.Ico (m-k) (m-k+k), u i (Function.update (w0 j) i x))
      Finset.univ_nonempty
    exact ⟨x, fun y => hx y (Finset.mem_univ _)⟩
  choose s0 hs0 using hex
  obtain ⟨r, hr, g, hg0, hgr, hge, hgc⟩ := ucb_short_nat u hu s0
  generalize LGamma u = L at hr hkm ⊢
  let w : ℕ → ∀ i, S i := ucbSeq h (fun n => g (n / k))
  have hwlt : ∀ j, j < m → w j = w0 j := by
    intro j hj; simp only [w, w0, ucbSeq, dif_pos hj]
  have hwge : ∀ j, m ≤ j → w j = g ((j - m) / k) := by
    intro j hj; simp only [w, ucbSeq, dif_neg (show ¬ j < m by omega)]
  have hkL : k * L + 2 * k ≤ m := by nlinarith
  have hkr : k * r ≤ k * L := Nat.mul_le_mul_left k hr
  have hη : ∀ i, ucbABR u w k (m-k) i (s0 i) := by
    intro i
    apply ucbABR_congr u w0 w k (m-k) i (s0 i) _ (hs0 i)
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact (hwlt j (by omega)).symm
  -- invariant
  have hinv : ∀ j ≤ r, ∀ i, ucbABR u w k (m-k) i (g j i) ∨
      ∃ c < j, IsBestReply u i (g c) (g j i) := by
    intro j
    induction j with
    | zero => intro _ i; left; rw [hg0]; exact hη i
    | succ j ih =>
      intro hj i
      obtain ⟨l, x, -, hbr, heq⟩ := hge j (by omega)
      by_cases hil : i = l
      · subst hil
        right
        refine ⟨j, by omega, ?_⟩
        rw [heq, Function.update_self]
        exact hbr
      · have hgi : g (j+1) i = g j i := by rw [heq, Function.update_of_ne hil]
        rw [hgi]
        rcases ih (by omega) i with h1 | ⟨c, hc, h2⟩
        · left; exact h1
        · right; exact ⟨c, by omega, h2⟩
  -- the step lemma
  have hstep : ∀ n i, ∃ a, n ≤ a ∧ a + k ≤ n + m ∧ ucbABR u w k a i (w (m+n) i) := by
    intro n i
    have hwn : w (m+n) = g (n / k) := by rw [hwge _ (by omega)]; congr 2; omega
    rw [hwn]
    have hlt : n < k * (n / k) + k := by
      have := Nat.lt_mul_div_succ n (show 0 < k by omega)
      rw [mul_add, mul_one] at this; exact this
    have hle : k * (n / k) ≤ n := Nat.mul_div_le n k
    by_cases hcase : r < n / k
    · have h1 : k * (r + 1) ≤ k * (n / k) := Nat.mul_le_mul_left k hcase
      rw [mul_add, mul_one] at h1
      refine ⟨n + m - k, by omega, by omega, ?_⟩
      rw [hgc _ hcase.le]
      apply ucbABR_const u w k _ i _ (g r) _ (ucb_strict_br u _ hgr i)
      intro j hj
      simp only [Finset.mem_Ico] at hj
      rw [hwge j (by omega)]
      apply hgc
      apply (Nat.le_div_iff_mul_le (by omega)).2
      rw [mul_comm]; omega
    · push_neg at hcase
      have h1 : k * (n / k + 1) ≤ k * (r + 1) := Nat.mul_le_mul_left k (by omega)
      rw [mul_add, mul_one, mul_add, mul_one] at h1
      rcases hinv (n / k) hcase i with h2 | ⟨c, hc, h3⟩
      · exact ⟨m - k, by omega, by omega, h2⟩
      · have h4 : k * (c + 1) ≤ k * (n / k) := Nat.mul_le_mul_left k hc
        have h5 : k * c ≤ k * r := Nat.mul_le_mul_left k (by omega)
        rw [mul_add, mul_one] at h4
        refine ⟨m + k * c, by omega, by omega, ?_⟩
        apply ucbABR_const u w k _ i _ (g c) _ h3
        intro j hj
        simp only [Finset.mem_Ico] at hj
        rw [hwge j (by omega)]
        congr 1
        apply Nat.div_eq_of_lt_le
        · rw [mul_comm]; omega
        · rw [Nat.succ_mul, mul_comm]; omega
  let st : ℕ → History S m := fun n t => w (t.val + n)
  have hst : ∀ n, 0 < adaptivePlay p (st n) (st (n+1)) := by
    intro n
    unfold adaptivePlay
    rw [if_pos]
    · apply Finset.prod_pos
      intro i _
      have e : st (n+1) ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩ = w (m + n) := by
        simp only [st]; congr 1; omega
      rw [e]
      obtain ⟨a, ha1, ha2, ha3⟩ := hstep n i
      exact (hp.2.2 i (st n) _).2 (ucb_sample u w k a n ha1 ha2 i _ ha3)
    · intro t ht
      simp only [st]; congr 1; omega
  have hc := ucb_chain p hp.1 st hst (k * L + m)
  have h0 : st 0 = h := by
    funext t; simp only [st, add_zero]; rw [hwlt _ t.2]; simp [w0, ucbSeq]
  have hM : st (k * L + m) = fun _ => g r := by
    funext t
    simp only [st]
    rw [hwge _ (by omega)]
    apply hgc
    apply (Nat.le_div_iff_mul_le (by omega)).2
    rw [mul_comm]; omega
  rw [h0, hM] at hc
  exact ⟨g r, hgr, hc⟩

theorem uniform_convention_bound_core (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p) :
    ∃ q : ℝ, 0 < q ∧ ∀ h : History S m,
      q ≤ ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ (k * LGamma u + m)) h h' := by
  have hpos : ∀ h : History S m, 0 < ∑ h' ∈ Finset.univ.filter
      (fun h' : History S m => IsConvention u h'), (adaptivePlay p ^ (k * LGamma u + m)) h h' := by
    intro h
    obtain ⟨s, hs, hpos⟩ := ucb_reach u hu k m hk hkm p hp h
    refine lt_of_lt_of_le hpos ?_
    apply Finset.single_le_sum (f := fun h' => (adaptivePlay p ^ (k * LGamma u + m)) h h')
    · intro z _; exact ucb_P_nonneg p hp.1 _ _ _
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s, hs, rfl⟩
  have hne : (Finset.univ : Finset (History S m)).Nonempty :=
    ⟨fun _ i => Classical.arbitrary _, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne (fun h => ∑ h' ∈ Finset.univ.filter
      (fun h' : History S m => IsConvention u h'), (adaptivePlay p ^ (k * LGamma u + m)) h h'),
    ?_, fun h => Finset.inf'_le _ (Finset.mem_univ h)⟩
  rw [Finset.lt_inf'_iff]
  intro h _; exact hpos h

theorem th1_rowsum {m : ℕ} [NeZero m] (p : ∀ i, History S m → S i → ℝ)
    (hp1 : ∀ i h, ∑ x, p i h x = 1) (h : History S m) :
    ∑ h', adaptivePlay p h h' = 1 := by
  have hm : 0 < m := NeZero.pos m
  unfold adaptivePlay
  rw [← Finset.sum_filter]
  rw [Finset.sum_nbij' (fun h' => h' ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩)
    (fun s => fun t => if ht : t.val + 1 < m then h ⟨t.val + 1, ht⟩ else s)
    (t := Finset.univ) (g := fun s => ∏ i, p i h (s i))]
  · rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun i _ => hp1 i h)
  · intro _ _; exact Finset.mem_univ _
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro t ht
    simp [dif_pos ht]
  · intro h' hh'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh'
    funext t
    by_cases ht : t.val + 1 < m
    · simp only [dif_pos ht]; exact (hh' t ht).symm
    · simp only [dif_neg ht]; congr 1; ext; simp; omega
  · intro s _
    simp only
    rw [dif_neg (by simp; omega)]
  · intro h' _; rfl

theorem th1_rowsum_pow {m : ℕ} [NeZero m] (p : ∀ i, History S m → S i → ℝ)
    (hp1 : ∀ i h, ∑ x, p i h x = 1) (n : ℕ) (h : History S m) :
    ∑ h', (adaptivePlay p ^ n) h h' = 1 := by
  induction n generalizing h with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    simp
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, th1_rowsum p hp1, mul_one]
    exact ih h

theorem th1_absorb (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (s : ∀ i, S i) (hs : IsStrictNash u s) :
    adaptivePlay p (fun _ => s) (fun _ => s) = 1 := by
  unfold adaptivePlay
  rw [if_pos (show IsSuccessor (fun _ => s) (fun _ => s : History S m) from fun t ht => rfl)]
  apply Finset.prod_eq_one
  intro i _
  have h1 := hp.2.1 i (fun _ => s)
  rw [Finset.sum_eq_single (s i)] at h1
  · exact h1
  · intro y _ hy
    apply le_antisymm _ (hp.1 i _ y)
    by_contra hpos
    push_neg at hpos
    obtain ⟨K, hK, hbr⟩ := (hp.2.2 i _ y).1 hpos
    have := hbr (s i)
    simp only [Finset.sum_const, nsmul_eq_mul, Function.update_eq_self, hK] at this
    have h2 := hs i y hy
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  · intro h; exact absurd (Finset.mem_univ _) h

theorem th1_absorb_pow (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (x : History S m) (hx : IsConvention u x) (n : ℕ) :
    1 ≤ ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ n) x h' := by
  obtain ⟨s, hs, rfl⟩ := hx
  have hpow : ∀ n, 1 ≤ (adaptivePlay p ^ n) (fun _ => s) (fun _ => s) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      calc (1:ℝ) ≤ (adaptivePlay p ^ n) (fun _ => s) (fun _ => s) *
            adaptivePlay p (fun _ => s) (fun _ => s) := by
            rw [th1_absorb u k m hk p hp s hs, mul_one]; exact ih
        _ ≤ _ := by
          apply Finset.single_le_sum (f := fun z => (adaptivePlay p ^ n) (fun _ => s) z *
            adaptivePlay p z (fun _ => s)) _ (Finset.mem_univ _)
          intro z _
          apply mul_nonneg (ucb_P_nonneg p hp.1 n _ _)
          simpa using ucb_P_nonneg p hp.1 1 z (fun _ => s)
  refine (hpow n).trans ?_
  apply Finset.single_le_sum (f := fun h' => (adaptivePlay p ^ n) (fun _ => s) h')
  · intro z _; exact ucb_P_nonneg p hp.1 _ _ _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s, hs, rfl⟩

theorem th1_split (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (t s : ℕ) (c : ℝ)
    (hc : ∀ x : History S m, ¬ IsConvention u x → c ≤
      ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ s) x h') (h : History S m) :
    ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ t) h h' +
      c * ∑ h' ∈ Finset.univ.filter (fun h' : History S m => ¬ IsConvention u h'),
        (adaptivePlay p ^ t) h h' ≤
    ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ (t + s)) h h' := by
  have e : ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
        (adaptivePlay p ^ (t + s)) h h' = ∑ x, (adaptivePlay p ^ t) h x *
          ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
            (adaptivePlay p ^ s) x h' := by
    simp only [pow_add, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [e, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : History S m => IsConvention u x), Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := th1_absorb_pow u k m hk p hp x hx s
    have h0 := ucb_P_nonneg p hp.1 t h x
    nlinarith
  · apply Finset.sum_le_sum
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := hc x hx
    have h0 := ucb_P_nonneg p hp.1 t h x
    nlinarith

theorem theorem_1_core (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    Tendsto (fun t : ℕ => ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ t) h h') atTop (𝓝 1) := by
  obtain ⟨q, hq, hqb⟩ := uniform_convention_bound_core u hu k m hk hkm p hp
  set M := k * LGamma u + m with hM
  have hMpos : 0 < M := by have := NeZero.pos m; omega
  clear_value M
  let A : ℕ → ℝ := fun t => ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ t) h h'
  let B : ℕ → ℝ := fun t => ∑ h' ∈ Finset.univ.filter
      (fun h' : History S m => ¬ IsConvention u h'), (adaptivePlay p ^ t) h h'
  have hAB : ∀ t, A t + B t = 1 := by
    intro t
    simp only [A, B]
    rw [Finset.sum_filter_add_sum_filter_not]
    exact th1_rowsum_pow p hp.2.1 t h
  have hB0 : ∀ t, 0 ≤ B t := fun t =>
    Finset.sum_nonneg (fun x _ => ucb_P_nonneg p hp.1 t h x)
  have hmono : ∀ t, B (t+1) ≤ B t := by
    intro t
    have := th1_split u k m hk p hp t 1 0 (fun x _ => Finset.sum_nonneg
      (fun y _ => ucb_P_nonneg p hp.1 1 x y)) h
    have e1 := hAB t
    have e2 := hAB (t+1)
    simp only [A, B] at e1 e2 ⊢
    linarith
  have hanti : Antitone B := antitone_nat_of_succ_le hmono
  have hq1 : q ≤ 1 := by
    have := hqb h
    have e := hAB M
    have := hB0 M
    simp only [A, B] at *
    linarith
  have hgeo : ∀ r : ℕ, B (r * M) ≤ (1 - q) ^ r := by
    intro r
    induction r with
    | zero =>
      have e := hAB 0
      have : 0 ≤ A 0 := Finset.sum_nonneg (fun x _ => ucb_P_nonneg p hp.1 0 h x)
      simp only [zero_mul, pow_zero]
      linarith
    | succ r ih =>
      have := th1_split u k m hk p hp (r * M) M q (fun x _ => hqb x) h
      have e1 := hAB (r * M)
      have e2 := hAB (r * M + M)
      rw [Nat.succ_mul, pow_succ]
      have : B (r * M + M) ≤ (1 - q) * B (r * M) := by
        simp only [A, B] at e1 e2 this ⊢
        nlinarith
      calc B (r * M + M) ≤ (1 - q) * B (r * M) := this
        _ ≤ (1 - q) * (1 - q) ^ r := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - q) ^ r * (1 - q) := by ring
  have hbound : ∀ t, 1 - (1 - q) ^ (t / M) ≤ A t := by
    intro t
    have h1 := hanti (Nat.div_mul_le_self t M)
    have h2 := hgeo (t / M)
    have e := hAB t
    linarith
  have hupper : ∀ t, A t ≤ 1 := by
    intro t; have := hAB t; have := hB0 t; linarith
  have hlim : Tendsto (fun t : ℕ => 1 - (1 - q) ^ (t / M)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℕ => t / M) atTop atTop := Nat.tendsto_div_const_atTop hMpos.ne'
    have h2 : Tendsto (fun n : ℕ => (1 - q) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    have := (h2.comp h1).const_sub 1
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hbound hupper

end UCB
end YoungConventions.AdaptivePlay

open YoungConventions.AdaptivePlay


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : WeaklyAcyclic u)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k * (LGamma u + 2) ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    Tendsto (fun t : ℕ => ∑ h' ∈ Finset.univ.filter (fun h' : History S m => IsConvention u h'),
      (adaptivePlay p ^ t) h h') atTop (𝓝 1) := by
  exact theorem_1_core u hu k m hk hkm p hp h
