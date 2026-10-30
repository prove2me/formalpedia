-- Prove2me | solution 1 for XuDRMDP.Finite.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T08:09:49.893815+00:00
-- url     : https://prove2.me/submissions/25e7b69f-60dc-448e-86a6-83b7a84bbe14

import Mathlib
import Definitions.Def_XuDRMDP_Finite_Setup
import Definitions.Def_XuDRMDP_Finite_Policies
import Definitions.Def_XuDRMDP_Finite_Ambiguity
import Definitions.Def_XuDRMDP_Finite_Returns
import Definitions.Def_XuDRMDP_Finite_Robustness
import Theorems.Thm_XuDRMDP_Finite_lemma_3_1
import Theorems.Thm_XuDRMDP_Finite_lemma_3_3

open MeasureTheory
open XuDRMDP.Finite
namespace XuT
noncomputable def cn {L : ℕ} (c : Fin (L+1) → ℝ) (k : ℕ) : ℝ := if h : k < L+1 then c ⟨k,h⟩ else 1
noncomputable def Dn {L : ℕ} (c : Fin (L+1) → ℝ) (k : ℕ) : ℝ := cn c k - if k = 0 then 0 else cn c (k-1)
noncomputable def Dl {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) : ℝ :=
  c i - if h : i.val = 0 then 0 else c ⟨i.val-1, by omega⟩

lemma Dl_eq {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) : Dl c i = Dn c i.val := by
  have h1 : i.val < L+1 := i.isLt
  unfold Dl Dn cn
  by_cases h0 : i.val = 0
  · simp [h0, h1]
    exact congrArg c (Fin.ext h0)
  · have h2 : i.val - 1 < L+1 := by omega
    simp [h0, h1, h2]

lemma sumD {L : ℕ} (c : Fin (L+1) → ℝ) (m : ℕ) : ∑ k ∈ Finset.range (m+1), Dn c k = cn c m := by
  induction m with
  | zero => simp [Dn]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Dn]

lemma cn_mono {L : ℕ} (c : Fin (L+1) → ℝ) (hm : Monotone c) (hl : c (Fin.last L) = 1) :
    Monotone (cn c) := by
  intro a b hab
  unfold cn
  by_cases hb : b < L+1
  · have ha : a < L+1 := lt_of_le_of_lt hab hb
    simp [ha, hb]
    exact hm hab
  · by_cases ha : a < L+1
    · simp [ha, hb]
      have : c ⟨a,ha⟩ ≤ c (Fin.last L) := hm (by rw [Fin.le_def]; simp; omega)
      linarith
    · simp [ha, hb]

lemma cn_nonneg {L : ℕ} (c : Fin (L+1) → ℝ) (hn : ∀ i, 0 ≤ c i) (k : ℕ) (hk : ¬ k < L + 1 → True): 0 ≤ cn c k := by
  unfold cn
  split_ifs with h
  · exact hn _
  · norm_num

lemma Dn_nonneg {L : ℕ} (c : Fin (L+1) → ℝ) (hn : ∀ i, 0 ≤ c i) (hm : Monotone c) (hl : c (Fin.last L) = 1) (k : ℕ) :
    0 ≤ Dn c k := by
  have hmo := cn_mono c hm hl
  unfold Dn
  split_ifs with h
  · simpa using cn_nonneg c hn k (fun _ => trivial)
  · have := hmo (Nat.sub_le k 1); linarith

lemma Dl_nonneg {L : ℕ} (c : Fin (L+1) → ℝ) (hn : ∀ i, 0 ≤ c i) (hm : Monotone c) (hl : c (Fin.last L) = 1) (i : Fin (L+1)) :
    0 ≤ Dl c i := by
  rw [Dl_eq]; exact Dn_nonneg c hn hm hl _

lemma sum_Dl {L : ℕ} (c : Fin (L+1) → ℝ) (hl : c (Fin.last L) = 1) : ∑ i, Dl c i = 1 := by
  simp_rw [Dl_eq]
  rw [Fin.sum_univ_eq_sum_range (fun k => Dn c k) (L+1), sumD]
  have : cn c L = 1 := by simp [cn]; exact hl
  simp [this]

lemma sum_Dl_le {L : ℕ} (c : Fin (L+1) → ℝ) (i : Fin (L+1)) :
    ∑ j : Fin (L+1), (if j ≤ i then Dl c j else 0) = c i := by
  have : ∀ j : Fin (L+1), (if j ≤ i then Dl c j else 0) = (fun k : ℕ => if k ≤ i.val then Dn c k else 0) j.val := by
    intro j; simp only [Fin.le_def, Dl_eq]
  simp_rw [this]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k ≤ i.val then Dn c k else 0) (L+1)]
  have h2 : ∑ k ∈ Finset.range (L+1), (if k ≤ i.val then Dn c k else 0) = ∑ k ∈ Finset.range (i.val+1), Dn c k := by
    rw [← Finset.sum_filter]
    have hf : Finset.filter (fun k => k ≤ i.val) (Finset.range (L+1)) = Finset.range (i.val+1) := by
      have := i.isLt
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hf]
  rw [h2, sumD]
  simp [cn, i.isLt]



section A
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G) (s : Fin n)

lemma cinc_eq (i : Fin (U.layers + 1)) : confidenceIncrement U i = Dl U.confidence i := rfl

lemma cinc_nonneg (i : Fin (U.layers + 1)) : 0 ≤ confidenceIncrement U i :=
  Dl_nonneg U.confidence U.confidence_nonneg U.confidence_mono U.confidence_last i

lemma cinc_sum : ∑ i, confidenceIncrement U i = 1 := sum_Dl U.confidence U.confidence_last

noncomputable def combL : (Fin (U.layers + 1) → Local n a s) →ₗ[ℝ] Local n a s :=
  ∑ i, confidenceIncrement U i • LinearMap.proj i

lemma combL_apply (y : Fin (U.layers + 1) → Local n a s) :
    combL U s y = ∑ i, confidenceIncrement U i • y i := by
  simp [combL]

lemma red_eq : reducedSet U s = (combL U s) '' Set.pi Set.univ (U.sets s) := by
  ext x
  simp only [reducedSet, Set.mem_setOf_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies,
    combL_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

lemma red_compact : IsCompact (reducedSet U s) := by
  rw [red_eq]
  exact (isCompact_univ_pi (fun i => U.compact s i)).image (LinearMap.continuous_of_finiteDimensional _)

lemma red_convex : Convex ℝ (reducedSet U s) := by
  rw [red_eq]
  exact (convex_pi (fun i _ => U.convex s i)).linear_image _

lemma red_nonempty : (reducedSet U s).Nonempty := by
  rw [red_eq]
  refine Set.Nonempty.image _ ?_
  have : ∀ i, ∃ y, y ∈ U.sets s i := fun i => U.nonempty s i
  choose y hy using this
  exact ⟨y, fun i _ => hy i⟩


lemma red_props {x : Local n a s} (hx : x ∈ reducedSet U s) :
    (∀ b j, 0 ≤ x.1 b j) ∧ (∀ b, ∑ j, x.1 b j = 1) ∧
    (G.stage s + 1 < G.horizon → ∀ b j, G.stage j ≠ G.stage s + 1 → x.1 b j = 0) := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hv := fun i => U.valid s i (y i) (hy i)
  have hnn : ∀ i b j, 0 ≤ (y i).1 b j := by
    intro i b j
    obtain ⟨⟨M, hM⟩, _, _⟩ := hv i
    have : (y i).1 b j = M.trans s b j := by rw [← hM]; rfl
    rw [this]; exact M.trans_nonneg _ _ _
  have hsum : ∀ i b, ∑ j, (y i).1 b j = 1 := by
    intro i b
    obtain ⟨⟨M, hM⟩, _, _⟩ := hv i
    have h1 : ∀ j, (y i).1 b j = M.trans s b j := by intro j; rw [← hM]; rfl
    simp_rw [h1]
    exact (hasSum_fintype (M.trans s b)).unique (M.trans_sum s b)
  have hz : ∀ i, G.stage s + 1 < G.horizon → ∀ b j, G.stage j ≠ G.stage s + 1 → (y i).1 b j = 0 :=
    fun i h b j hj => (hv i).2.2 h b j hj
  have hcoord : ∀ b j, (∑ i, confidenceIncrement U i • y i).1 b j =
      ∑ i, confidenceIncrement U i * (y i).1 b j := by
    intro b j; simp [Prod.fst_sum, Finset.sum_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro b j; rw [hcoord]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (cinc_nonneg U i) (hnn i b j)
  · intro b
    simp_rw [hcoord]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hsum, mul_one]
    exact cinc_sum U
  · intro h b j hj
    rw [hcoord]
    exact Finset.sum_eq_zero fun i _ => by rw [hz i h b j hj, mul_zero]

end A

section minimax
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma minimax_eps {m : ℕ} [NeZero m] {X : Set E} (hc : IsCompact X) (hcv : Convex ℝ X)
    (g : E →ₗ[ℝ] (Fin m → ℝ)) (hg : Continuous g) (w : ℝ)
    (hw : ∀ x ∈ X, w ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => g x b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin m → ℝ, q ∈ stdSimplex ℝ (Fin m) ∧ ∀ x ∈ X, w - ε ≤ ∑ b, q b * g x b := by
  by_cases hXe : X.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hXe
    refine ⟨fun _ => 1 / (m : ℝ), ⟨fun _ => by positivity, ?_⟩, by simp [hXe]⟩
    have : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    simp [this]
  set T : Set (Fin m → ℝ) := g '' X with hT
  set O : Set (Fin m → ℝ) := {y | ∀ b, y b ≤ w - ε} with hO
  have hTc : IsCompact T := hc.image hg
  have hTcv : Convex ℝ T := hcv.linear_image g
  have hOcv : Convex ℝ O := by
    intro y hy z hz s t hs ht hst b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hy b) hs
    have h2 := mul_le_mul_of_nonneg_left (hz b) ht
    have h3 : s * (w - ε) + t * (w - ε) = w - ε := by rw [← add_mul, hst, one_mul]
    linarith
  have hOcl : IsClosed O := by
    have : O = ⋂ b, {y : Fin m → ℝ | y b ≤ w - ε} := by ext y; simp [hO]
    rw [this]
    exact isClosed_iInter fun b => isClosed_le (continuous_apply b) continuous_const
  have hdisj : Disjoint T O := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxO
    have h1 : Finset.univ.sup' Finset.univ_nonempty (fun b => g x b) ≤ w - ε :=
      Finset.sup'_le _ _ fun b _ => hxO b
    linarith [hw x hx]
  obtain ⟨f, u, v, hfT, huv, hfO⟩ := geometric_hahn_banach_compact_closed hTcv hTc hOcv hOcl hdisj
  have hf : ∀ y : Fin m → ℝ, f y = ∑ b, y b * f (Pi.single b 1) := by
    intro y
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) y
    have e : ∀ x : Fin m, (fun j => if x = j then (1:ℝ) else 0) = Pi.single x 1 := by
      intro x; ext j; by_cases h : x = j <;> simp [Pi.single_apply, h, eq_comm]
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    simp only [smul_eq_mul, e]
    rfl
  set l : Fin m → ℝ := fun b => f (Pi.single b 1) with hl
  have hf' : ∀ y : Fin m → ℝ, f y = ∑ b, y b * l b := hf
  set base : Fin m → ℝ := fun _ => w - ε with hbase_def
  have hbase : base ∈ O := fun b => le_rfl
  have hlneg : ∀ b, l b ≤ 0 := by
    intro b
    by_contra hpos
    push Not at hpos
    set t : ℝ := (f base - v) / l b + 1 with ht
    have hmem : base - t • Pi.single b (1 : ℝ) ∈ O := by
      intro b'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hbase_def]
      have hv := hfO base hbase
      have ht0 : 0 ≤ t := by
        have : 0 ≤ (f base - v) / l b := div_nonneg (by linarith) hpos.le
        linarith
      have : 0 ≤ t * (Pi.single b (1 : ℝ) : Fin m → ℝ) b' := by
        by_cases hb : b' = b
        · subst hb; simp [ht0]
        · simp [hb]
      linarith
    have h1 := hfO _ hmem
    rw [map_sub, map_smul] at h1
    have h2 : f (Pi.single b (1 : ℝ)) = l b := rfl
    rw [h2, smul_eq_mul] at h1
    have h3 : t * l b = f base - v + l b := by
      rw [ht]; field_simp
    linarith
  obtain ⟨x1, hx1⟩ := hXe
  have hsumpos : 0 < -∑ b, l b := by
    by_contra hnot
    push Not at hnot
    have hz : ∀ b, l b = 0 := by
      intro b
      have : ∑ b, l b = 0 := by
        have h0 : ∑ b, l b ≤ 0 := Finset.sum_nonpos fun b _ => hlneg b
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hlneg b)).1 this b (Finset.mem_univ b)
      exact this
    have e1 := hfT (g x1) ⟨x1, hx1, rfl⟩
    have e2 := hfO base hbase
    rw [hf' (g x1)] at e1
    rw [hf' base] at e2
    simp [hz] at e1 e2
    linarith
  set c : ℝ := -∑ b, l b with hc_def
  refine ⟨fun b => -l b / c, ⟨fun b => div_nonneg (by linarith [hlneg b]) hsumpos.le, ?_⟩, ?_⟩
  · simp only
    rw [← Finset.sum_div, Finset.sum_neg_distrib, div_self hsumpos.ne']
  · intro x hx
    have e1 := hfT (g x) ⟨x, hx, rfl⟩
    have e2 := hfO base hbase
    rw [hf' (g x)] at e1
    rw [hf' base] at e2
    have e3 : ∑ b, g x b * l b = -c * ∑ b, (-l b / c) * g x b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      field_simp
    have e4 : ∑ b, base b * l b = -c * (w - ε) := by
      simp only [hbase_def]
      rw [← Finset.mul_sum, hc_def]; ring
    rw [e3] at e1
    rw [e4] at e2
    nlinarith


lemma minimax_main {m : ℕ} [NeZero m] {X : Set E} (hc : IsCompact X) (hcv : Convex ℝ X)
    (hne : X.Nonempty) (g : E →ₗ[ℝ] (Fin m → ℝ)) (hg : Continuous g)
    (Qs : Set (Fin m → ℝ))
    (hQs : ∀ q ∈ Qs, q ∈ stdSimplex ℝ (Fin m) ∧ ∀ q' ∈ stdSimplex ℝ (Fin m),
      sInf ((fun x => ∑ b, q' b * g x b) '' X) ≤ sInf ((fun x => ∑ b, q b * g x b) '' X)) :
    ∃ x0 ∈ X, ∀ q ∈ Qs, (∀ q' ∈ stdSimplex ℝ (Fin m), ∑ b, q' b * g x0 b ≤ ∑ b, q b * g x0 b) ∧
      (∀ x ∈ X, ∑ b, q b * g x0 b ≤ ∑ b, q b * g x b) ∧
      ∑ b, q b * g x0 b = sInf ((fun x => ∑ b, q b * g x b) '' X) := by
  set φ : E → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty (fun b => g x b) with hφ
  have hφc : Continuous φ := by
    apply Continuous.finset_sup'_apply
    intro b _
    exact (continuous_apply b).comp hg
  obtain ⟨x0, hx0, hmin⟩ := hc.exists_isMinOn hne hφc.continuousOn
  have hmin' : ∀ x ∈ X, φ x0 ≤ φ x := fun x hx => hmin hx
  have hbdd : ∀ q : Fin m → ℝ, BddBelow ((fun x => ∑ b, q b * g x b) '' X) := by
    intro q
    refine (hc.image ?_).bddBelow
    exact continuous_finset_sum _ fun b _ => continuous_const.mul ((continuous_apply b).comp hg)
  have hupper : ∀ q' ∈ stdSimplex ℝ (Fin m), ∑ b, q' b * g x0 b ≤ φ x0 := by
    intro q' hq'
    calc ∑ b, q' b * g x0 b ≤ ∑ b, q' b * φ x0 :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun b => g x0 b) (Finset.mem_univ b)) (hq'.1 b)
      _ = φ x0 := by rw [← Finset.sum_mul, hq'.2, one_mul]
  refine ⟨x0, hx0, fun q hq => ?_⟩
  obtain ⟨hqs, hqmax⟩ := hQs q hq
  have hFge : φ x0 ≤ sInf ((fun x => ∑ b, q b * g x b) '' X) := by
    refine le_of_forall_sub_le fun ε hε => ?_
    obtain ⟨qe, hqe, hqex⟩ := minimax_eps hc hcv g hg (φ x0) hmin' ε hε
    have h1 : φ x0 - ε ≤ sInf ((fun x => ∑ b, qe b * g x b) '' X) :=
      le_csInf (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hqex x hx)
    linarith [hqmax qe hqe]
  have hFle : sInf ((fun x => ∑ b, q b * g x b) '' X) ≤ ∑ b, q b * g x0 b :=
    csInf_le (hbdd q) ⟨x0, hx0, rfl⟩
  have hup := hupper q hqs
  refine ⟨fun q' hq' => ?_, fun x hx => ?_, ?_⟩
  · linarith [hupper q' hq']
  · have := csInf_le (hbdd q) ⟨x, hx, rfl⟩
    linarith
  · linarith

end minimax

section B
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G) (s : Fin n)

noncomputable def gL (G : Setup n a) (s : Fin n) (v : Fin n → ℝ) :
    Local n a s →ₗ[ℝ] (Fin (a s) → ℝ) where
  toFun x b := x.2 b + G.discount * ∑ j, x.1 b j * v j
  map_add' x y := by
    ext b
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    ext b
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, ← Finset.mul_sum]
    ring

lemma av_eq (q : MixedAction a s) (x : Local n a s) (v : Fin n → ℝ) :
    actionValue G s q x v = ∑ b, q.val b * gL G s v x b := rfl

lemma state_x0 (v : Fin n → ℝ) (Qs : Set (MixedAction a s))
    (hQ : ∀ q ∈ Qs, ∀ q' : MixedAction a s,
      lowerActionValue U s q' v ≤ lowerActionValue U s q v) :
    ∃ x0 ∈ reducedSet U s, ∀ q ∈ Qs,
      (∀ q' : MixedAction a s, actionValue G s q' x0 v ≤ actionValue G s q x0 v) ∧
      (∀ x ∈ reducedSet U s, actionValue G s q x0 v ≤ actionValue G s q x v) ∧
      actionValue G s q x0 v = lowerActionValue U s q v := by
  have hg : Continuous (gL G s v) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨x0, hx0, h⟩ := minimax_main (red_compact U s) (red_convex U s) (red_nonempty U s)
    (gL G s v) hg (Set.image (fun q : MixedAction a s => q.val) Qs) (by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨q.property, fun q' hq' => ?_⟩
      exact hQ q hq ⟨q', hq'⟩)
  refine ⟨x0, hx0, fun q hq => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h q.val ⟨q, hq, rfl⟩
  exact ⟨fun q' => h1 q'.val q'.property, h2, h3⟩

end B

section C
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G)

lemma rv_terminal (s : Fin n) (hnt : ¬ G.stage s + 1 < G.horizon) : robustValue U s = 0 := by
  have h0 : G.horizon - 1 - G.stage s = 0 := by have := G.stage_lt s; omega
  unfold robustValue
  rw [h0]; rfl

lemma rv_unfold (s : Fin n) (hnt : G.stage s + 1 < G.horizon) :
    robustValue U s = sSup (Set.range fun q : MixedAction a s =>
      lowerActionValue U s q (backward U (G.horizon - 2 - G.stage s))) := by
  unfold robustValue
  have : G.horizon - 1 - G.stage s = (G.horizon - 2 - G.stage s) + 1 := by omega
  rw [this, backward, if_pos hnt]

lemma backward_next (s j : Fin n) (hnt : G.stage s + 1 < G.horizon)
    (hj : G.stage j = G.stage s + 1) : backward U (G.horizon - 2 - G.stage s) j = robustValue U j := by
  unfold robustValue
  have : G.horizon - 1 - G.stage j = G.horizon - 2 - G.stage s := by omega
  rw [this]

lemma av_backward (s : Fin n) (hnt : G.stage s + 1 < G.horizon) (q : MixedAction a s)
    {x : Local n a s} (hx : x ∈ reducedSet U s) :
    actionValue G s q x (backward U (G.horizon - 2 - G.stage s)) =
      actionValue G s q x (robustValue U) := by
  obtain ⟨_, _, hz⟩ := red_props U s hx
  unfold actionValue
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∑ j, x.1 b j * backward U (G.horizon - 2 - G.stage s) j =
      ∑ j, x.1 b j * robustValue U j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : G.stage j = G.stage s + 1
    · rw [backward_next U s j hnt hj]
    · rw [hz hnt b j hj, zero_mul, zero_mul]
  rw [this]

lemma lower_backward (s : Fin n) (hnt : G.stage s + 1 < G.horizon) (q : MixedAction a s) :
    lowerActionValue U s q (backward U (G.horizon - 2 - G.stage s)) =
      lowerActionValue U s q (robustValue U) := by
  unfold lowerActionValue
  congr 1
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (av_backward U s hnt q hx).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, av_backward U s hnt q hx⟩

lemma rv_eq_lower {π : Policy a} (hπ : SRobust U π) (h : History a) (hh : Admissible G h)
    (hnt : G.stage h.state + 1 < G.horizon) :
    robustValue U h.state = lowerActionValue U h.state (π h) (robustValue U) := by
  rw [rv_unfold U h.state hnt]
  simp_rw [lower_backward U h.state hnt]
  refine IsGreatest.csSup_eq ⟨⟨π h, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hπ h hh hnt q

end C

section D
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G)

noncomputable def Tstep (G : Setup n a) (h : History a) (x : Local n a h.state)
    (W : History a → ℝ) (b : Fin (a h.state)) : ℝ :=
  x.2 b + G.discount * ∑ j : Fin n,
    if G.stage j = G.stage h.state + 1 then x.1 b j * W (h.extend b j) else 0

lemma dp_induct (P : History a → Prop)
    (hP : ∀ h, Admissible G h →
      (G.stage h.state + 1 < G.horizon → ∀ b j, G.stage j = G.stage h.state + 1 →
        P (h.extend b j)) → P h) :
    ∀ h, Admissible G h → P h := by
  have key : ∀ k, ∀ h, Admissible G h → G.horizon - G.stage h.state ≤ k → P h := by
    intro k
    induction k with
    | zero => intro h _ hk; have := G.stage_lt h.state; omega
    | succ k ih =>
      intro h hh hk
      apply hP h hh
      intro hnt b j hj
      refine ih _ (hh.extend b j hj) ?_
      show G.horizon - G.stage j ≤ k
      omega
  exact fun h hh => key _ h hh le_rfl

lemma Tstep_le (h : History a) {x : Local n a h.state} (hx : x ∈ reducedSet U h.state)
    (hnt : G.stage h.state + 1 < G.horizon) (W : History a → ℝ) (v : Fin n → ℝ)
    (b : Fin (a h.state))
    (hW : ∀ j, G.stage j = G.stage h.state + 1 → W (h.extend b j) ≤ v j) :
    Tstep G h x W b ≤ gL G h.state v x b := by
  obtain ⟨hnn, _, hz⟩ := red_props U h.state hx
  show x.2 b + G.discount * _ ≤ x.2 b + G.discount * ∑ j, x.1 b j * v j
  have : ∑ j : Fin n, (if G.stage j = G.stage h.state + 1 then x.1 b j * W (h.extend b j) else 0)
      ≤ ∑ j, x.1 b j * v j := Finset.sum_le_sum fun j _ => by
    by_cases hj : G.stage j = G.stage h.state + 1
    · rw [if_pos hj]; exact mul_le_mul_of_nonneg_left (hW j hj) (hnn b j)
    · rw [if_neg hj, hz hnt b j hj]; simp
  exact add_le_add_right (mul_le_mul_of_nonneg_left this G.discount_pos.le) _

lemma Tstep_ge (h : History a) {x : Local n a h.state} (hx : x ∈ reducedSet U h.state)
    (hnt : G.stage h.state + 1 < G.horizon) (W : History a → ℝ) (v : Fin n → ℝ)
    (b : Fin (a h.state))
    (hW : ∀ j, G.stage j = G.stage h.state + 1 → v j ≤ W (h.extend b j)) :
    gL G h.state v x b ≤ Tstep G h x W b := by
  obtain ⟨hnn, _, hz⟩ := red_props U h.state hx
  show x.2 b + G.discount * ∑ j, x.1 b j * v j ≤ x.2 b + G.discount * _
  have : ∑ j, x.1 b j * v j ≤ ∑ j : Fin n,
      (if G.stage j = G.stage h.state + 1 then x.1 b j * W (h.extend b j) else 0) :=
    Finset.sum_le_sum fun j _ => by
    by_cases hj : G.stage j = G.stage h.state + 1
    · rw [if_pos hj]; exact mul_le_mul_of_nonneg_left (hW j hj) (hnn b j)
    · rw [if_neg hj, hz hnt b j hj]; simp
  exact add_le_add_right (mul_le_mul_of_nonneg_left this G.discount_pos.le) _


lemma mean_pi (μ : Marginals n a) (hμ : ∀ s, IsProbabilityMeasure (μ s)) (s : Fin n) :
    globalMean (productLaw μ) s = localMean (μ s) := by
  unfold globalMean productLaw localMean
  exact integral_eval

lemma exp_term (π' : Policy a) (ν : Measure (Parameters n a)) (h : History a)
    (hnt : ¬ G.stage h.state + 1 < G.horizon) : expectedFrom G π' ν h = 0 := by
  have h0 : G.horizon - 1 - G.stage h.state = 0 := by have := G.stage_lt h.state; omega
  have rz : ∀ (k : ℕ) (hk : k = 0) (x : Parameters n a),
      (∑ z : Suffix a k, ∑ j : Fin n,
        trajectoryProbability G π' x h z j * trajectoryReward G x z) = 0 := by
    intro k hk x; subst hk; simp [trajectoryReward]
  have : ∀ x, returnFrom G π' x h = 0 := fun x => rz _ h0 x
  unfold expectedFrom
  simp [this]

lemma exp_rec (μ : Marginals n a) (hμ : admissibleMarginals U μ) (π' : Policy a) (h : History a)
    (hh : Admissible G h) (hnt : G.stage h.state + 1 < G.horizon) :
    expectedFrom G π' (productLaw μ) h =
      ∑ b, (π' h).val b * Tstep G h (localMean (μ h.state)) (expectedFrom G π' (productLaw μ)) b := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := fun s => (hμ s).1
  obtain ⟨h1, h2⟩ := lemma_3_1 G U π' μ hμ h hh hnt
  rw [h1, h2, mean_pi μ this]
  rfl

end D

section E
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G)

lemma lav_le (s : Fin n) (q : MixedAction a s) (v : Fin n → ℝ) {x : Local n a s}
    (hx : x ∈ reducedSet U s) :
    lowerActionValue U s q v ≤ actionValue G s q x v := by
  unfold lowerActionValue
  refine csInf_le ?_ ⟨x, hx, rfl⟩
  refine ((red_compact U s).image ?_).bddBelow
  have hg : Continuous (gL G s v) := LinearMap.continuous_of_finiteDimensional _
  show Continuous fun x => ∑ b, q.val b * gL G s v x b
  exact continuous_finset_sum _ fun b _ => continuous_const.mul ((continuous_apply b).comp hg)

lemma dp_upper (π' : Policy a) (xs : Parameters n a) (hxs : ∀ s, xs s ∈ reducedSet U s)
    (W : History a → ℝ)
    (hrec : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      W h = ∑ b, (π' h).val b * Tstep G h (xs h.state) W b)
    (hterm : ∀ h, Admissible G h → ¬ G.stage h.state + 1 < G.horizon → W h = 0)
    (hmax : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      ∀ q' : MixedAction a h.state,
        actionValue G h.state q' (xs h.state) (robustValue U) ≤ robustValue U h.state) :
    ∀ h, Admissible G h → W h ≤ robustValue U h.state := by
  apply dp_induct
  intro h hh ih
  by_cases hnt : G.stage h.state + 1 < G.horizon
  · rw [hrec h hh hnt]
    calc _ ≤ ∑ b, (π' h).val b * gL G h.state (robustValue U) (xs h.state) b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (Tstep_le U h (hxs _) hnt W _ b fun j hj => ih hnt b j hj) ((π' h).property.1 b)
      _ = actionValue G h.state (π' h) (xs h.state) (robustValue U) := rfl
      _ ≤ _ := hmax h hh hnt _
  · rw [hterm h hh hnt, rv_terminal U _ hnt]

lemma dp_eq (π' : Policy a) (xs : Parameters n a) (hxs : ∀ s, xs s ∈ reducedSet U s)
    (W : History a → ℝ)
    (hrec : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      W h = ∑ b, (π' h).val b * Tstep G h (xs h.state) W b)
    (hterm : ∀ h, Admissible G h → ¬ G.stage h.state + 1 < G.horizon → W h = 0)
    (heq : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
        actionValue G h.state (π' h) (xs h.state) (robustValue U) = robustValue U h.state) :
    ∀ h, Admissible G h → W h = robustValue U h.state := by
  apply dp_induct
  intro h hh ih
  by_cases hnt : G.stage h.state + 1 < G.horizon
  · rw [hrec h hh hnt, ← heq h hh hnt]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact le_antisymm
      (Tstep_le U h (hxs _) hnt W _ b fun j hj => (ih hnt b j hj).le)
      (Tstep_ge U h (hxs _) hnt W _ b fun j hj => (ih hnt b j hj).ge)
  · rw [hterm h hh hnt, rv_terminal U _ hnt]

lemma dp_lower (π' : Policy a) (xs : Parameters n a) (hxs : ∀ s, xs s ∈ reducedSet U s)
    (W : History a → ℝ)
    (hrec : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      W h = ∑ b, (π' h).val b * Tstep G h (xs h.state) W b)
    (hterm : ∀ h, Admissible G h → ¬ G.stage h.state + 1 < G.horizon → W h = 0)
    (hlow : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
        robustValue U h.state ≤ actionValue G h.state (π' h) (xs h.state) (robustValue U)) :
    ∀ h, Admissible G h → robustValue U h.state ≤ W h := by
  apply dp_induct
  intro h hh ih
  by_cases hnt : G.stage h.state + 1 < G.horizon
  · rw [hrec h hh hnt]
    calc robustValue U h.state ≤ actionValue G h.state (π' h) (xs h.state) (robustValue U) :=
          hlow h hh hnt
      _ = ∑ b, (π' h).val b * gL G h.state (robustValue U) (xs h.state) b := rfl
      _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
            (Tstep_ge U h (hxs _) hnt W _ b fun j hj => ih hnt b j hj) ((π' h).property.1 b)
  · rw [hterm h hh hnt, rv_terminal U _ hnt]

lemma dp_bound {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ s, ∀ x ∈ reducedSet U s, ∀ b, |x.2 b| ≤ R)
    (π' : Policy a) (xs : Parameters n a) (hxs : ∀ s, xs s ∈ reducedSet U s)
    (W : History a → ℝ)
    (hrec : ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      W h = ∑ b, (π' h).val b * Tstep G h (xs h.state) W b)
    (hterm : ∀ h, Admissible G h → ¬ G.stage h.state + 1 < G.horizon → W h = 0) :
    ∀ h, Admissible G h → |W h| ≤ R * ((G.horizon - G.stage h.state : ℕ) : ℝ) := by
  apply dp_induct
  intro h hh ih
  by_cases hnt : G.stage h.state + 1 < G.horizon
  · obtain ⟨m, hm⟩ : ∃ m, G.horizon - G.stage h.state = m + 1 := ⟨G.horizon - G.stage h.state - 1, by omega⟩
    rw [hm]
    have hch : ∀ j, G.stage j = G.stage h.state + 1 → G.horizon - G.stage j = m := by
      intro j hj; omega
    have hb : ∀ b, |Tstep G h (xs h.state) W b| ≤ R * ((m + 1 : ℕ) : ℝ) := by
      intro b
      obtain ⟨hnn, hsum, hz⟩ := red_props U h.state (hxs h.state)
      have hS : |∑ j : Fin n, if G.stage j = G.stage h.state + 1
            then (xs h.state).1 b j * W (h.extend b j) else 0| ≤ R * m := by
        calc _ ≤ ∑ j : Fin n, |if G.stage j = G.stage h.state + 1
            then (xs h.state).1 b j * W (h.extend b j) else 0| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin n, (xs h.state).1 b j * (R * m) := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases hj : G.stage j = G.stage h.state + 1
            · rw [if_pos hj, abs_mul, abs_of_nonneg (hnn b j)]
              have := ih hnt b j hj
              have h2 : (((G.horizon - G.stage j : ℕ)) : ℝ) = m := by rw [hch j hj]
              refine mul_le_mul_of_nonneg_left ?_ (hnn b j)
              have h3 : |W (h.extend b j)| ≤ R * (((G.horizon - G.stage (h.extend b j).state : ℕ)) : ℝ) := this
              rw [show (h.extend b j).state = j from rfl, h2] at h3
              exact h3
            · rw [if_neg hj, abs_zero]
              exact mul_nonneg (hnn b j) (mul_nonneg hR0 (Nat.cast_nonneg _))
          _ = R * m := by rw [← Finset.sum_mul, hsum b, one_mul]
      have hr := hR h.state (xs h.state) (hxs h.state) b
      have hγ := G.discount_pos
      have hγ1 := G.discount_le_one
      unfold Tstep
      push_cast
      calc _ ≤ |(xs h.state).2 b| + |G.discount * ∑ j : Fin n, if G.stage j = G.stage h.state + 1
            then (xs h.state).1 b j * W (h.extend b j) else 0| := abs_add_le _ _
        _ ≤ R + R * m := by
          refine add_le_add hr ?_
          rw [abs_mul, abs_of_pos hγ]
          calc _ ≤ 1 * (R * m) := mul_le_mul hγ1 hS (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        _ = _ := by ring
    rw [hrec h hh hnt]
    calc _ ≤ ∑ b, |(π' h).val b * Tstep G h (xs h.state) W b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, (π' h).val b * (R * ((m + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg ((π' h).property.1 b)]
        exact mul_le_mul_of_nonneg_left (hb b) ((π' h).property.1 b)
      _ = R * ((m + 1 : ℕ) : ℝ) := by rw [← Finset.sum_mul, (π' h).property.2, one_mul]
  · rw [hterm h hh hnt, abs_zero]
    exact mul_nonneg hR0 (Nat.cast_nonneg _)

lemma exists_R : ∃ R : ℝ, 0 ≤ R ∧ ∀ s, ∀ x ∈ reducedSet U s, ∀ b, |x.2 b| ≤ R := by
  have : ∀ s, ∃ Rs : ℝ, ∀ x ∈ reducedSet U s, ‖x‖ ≤ Rs := fun s =>
    isBounded_iff_forall_norm_le.1 (red_compact U s).isBounded
  choose Rf hRf using this
  refine ⟨∑ s, |Rf s|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun s x hx b => ?_⟩
  calc |x.2 b| = ‖x.2 b‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖x.2‖ := norm_le_pi_norm _ _
    _ ≤ ‖x‖ := norm_snd_le x
    _ ≤ Rf s := hRf s x hx
    _ ≤ |Rf s| := le_abs_self _
    _ ≤ ∑ s, |Rf s| := Finset.single_le_sum (f := fun s => |Rf s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

end E

section F
variable {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)] {G : Setup n a}
  (U : Uncertainty G)

lemma exists_xs (π : Policy a) (hπ : SRobust U π) :
    ∃ xs : Parameters n a, (∀ s, xs s ∈ reducedSet U s) ∧
      ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
        (∀ q' : MixedAction a h.state,
          actionValue G h.state q' (xs h.state) (robustValue U) ≤ robustValue U h.state) ∧
        actionValue G h.state (π h) (xs h.state) (robustValue U) = robustValue U h.state := by
  let Qs : ∀ s, Set (MixedAction a s) := fun s => {q | ∃ h : History a, Admissible G h ∧
    G.stage h.state + 1 < G.horizon ∧ ∃ hs : h.state = s, q = hs ▸ π h}
  have hs : ∀ s : Fin n, ∃ x0 ∈ reducedSet U s, ∀ q ∈ Qs s,
      (∀ q' : MixedAction a s, actionValue G s q' x0 (robustValue U) ≤
        actionValue G s q x0 (robustValue U)) ∧
      (∀ x ∈ reducedSet U s, actionValue G s q x0 (robustValue U) ≤
        actionValue G s q x (robustValue U)) ∧
      actionValue G s q x0 (robustValue U) = lowerActionValue U s q (robustValue U) := by
    intro s
    apply state_x0 U s (robustValue U) (Qs s)
    rintro q ⟨h, hh, hnt, hs, rfl⟩ q'
    subst hs
    exact hπ h hh hnt q'
  choose xs hxm hxq using hs
  refine ⟨xs, hxm, fun h hh hnt => ?_⟩
  obtain ⟨c1, _, c3⟩ := hxq h.state (π h) ⟨h, hh, hnt, rfl, rfl⟩
  have e : actionValue G h.state (π h) (xs h.state) (robustValue U) = robustValue U h.state := by
    rw [c3, ← rv_eq_lower U hπ h hh hnt]
  exact ⟨fun q' => (c1 q').trans e.le, e⟩

theorem main_thm (U : Uncertainty G) (π : Policy a) (hπ : SRobust U π) :
    DistributionallyRobust U π ∧ ∃ ν : Measure (Parameters n a), Saddle U π ν := by
  obtain ⟨xs, hxm, hxs⟩ := exists_xs U π hπ
  have hμ : ∀ s, ∃ μ ∈ localClass U s, localMean μ = xs s := fun s => by
    have h2 : xs s ∈ {x | ∃ μ ∈ localClass U s, localMean μ = x} := by
      rw [lemma_3_3 G U s]; exact hxm s
    exact h2
  choose μ0 hμ0 hμ0m using hμ
  have hadm : admissibleMarginals U μ0 := hμ0
  have hX : ∀ μ, admissibleMarginals U μ → ∀ s, localMean (μ s) ∈ reducedSet U s :=
    fun μ hμ s => by rw [← lemma_3_3 G U s]; exact ⟨μ s, hμ s, rfl⟩
  have hrec : ∀ μ, admissibleMarginals U μ → ∀ π' : Policy a, ∀ h, Admissible G h →
      G.stage h.state + 1 < G.horizon →
      expectedFrom G π' (productLaw μ) h = ∑ b, (π' h).val b *
        Tstep G h (localMean (μ h.state)) (expectedFrom G π' (productLaw μ)) b :=
    fun μ hμ π' h hh hnt => exp_rec U μ hμ π' h hh hnt
  have hrec0 : ∀ π' : Policy a, ∀ h, Admissible G h → G.stage h.state + 1 < G.horizon →
      expectedFrom G π' (productLaw μ0) h = ∑ b, (π' h).val b *
        Tstep G h (xs h.state) (expectedFrom G π' (productLaw μ0)) b := by
    intro π' h hh hnt
    have := hrec μ0 hadm π' h hh hnt
    rw [hμ0m h.state] at this
    exact this
  have hup : ∀ π' : Policy a, performance G π' (productLaw μ0) ≤ robustValue U G.initial := by
    intro π'
    exact dp_upper U π' xs hxm _ (hrec0 π') (fun h _ hnt => exp_term π' _ h hnt)
      (fun h hh hnt => (hxs h hh hnt).1) (initialHistory G) Admissible.initial
  have heq : performance G π (productLaw μ0) = robustValue U G.initial :=
    dp_eq U π xs hxm _ (hrec0 π) (fun h _ hnt => exp_term π _ h hnt)
      (fun h hh hnt => (hxs h hh hnt).2) (initialHistory G) Admissible.initial
  have hlowν : ∀ ν' ∈ globalClass U, robustValue U G.initial ≤ performance G π ν' := by
    rintro _ ⟨μ', hμ', rfl⟩
    exact dp_lower U π (fun s => localMean (μ' s)) (hX μ' hμ') _ (hrec μ' hμ' π)
      (fun h _ hnt => exp_term π _ h hnt)
      (fun h hh hnt => (rv_eq_lower U hπ h hh hnt).le.trans (lav_le U _ _ _ (hX μ' hμ' _)))
      (initialHistory G) Admissible.initial
  have hmem : productLaw μ0 ∈ globalClass U := ⟨μ0, hadm, rfl⟩
  obtain ⟨R, hR0, hR⟩ := exists_R U
  have hbdd : ∀ π' : Policy a, BddBelow ((fun ν => performance G π' ν) '' globalClass U) := by
    intro π'
    refine ⟨-(R * (((G.horizon - G.stage (initialHistory G).state : ℕ)) : ℝ)), ?_⟩
    rintro _ ⟨_, ⟨μ', hμ', rfl⟩, rfl⟩
    have := dp_bound U hR0 hR π' (fun s => localMean (μ' s)) (hX μ' hμ') _ (hrec μ' hμ' π')
      (fun h _ hnt => exp_term π' _ h hnt) (initialHistory G) Admissible.initial
    exact (abs_le.1 this).1
  refine ⟨fun π' => ?_, productLaw μ0, hmem, fun π' => ?_, fun ν' hν' => ?_⟩
  · unfold worstPerformance
    calc _ ≤ performance G π' (productLaw μ0) := csInf_le (hbdd π') ⟨_, hmem, rfl⟩
      _ ≤ performance G π (productLaw μ0) := (hup π').trans heq.symm.le
      _ ≤ _ := by
        refine le_csInf ⟨_, productLaw μ0, hmem, rfl⟩ ?_
        rintro _ ⟨ν', hν', rfl⟩
        exact heq.le.trans (hlowν ν' hν')
  · rw [heq]; exact hup π'
  · rw [heq]; exact hlowν ν' hν'

end F
end XuT

theorem solution {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : XuDRMDP.Finite.Setup n a) (U : XuDRMDP.Finite.Uncertainty G)
    (π : XuDRMDP.Finite.Policy a) (hπ : XuDRMDP.Finite.SRobust U π) :
    XuDRMDP.Finite.DistributionallyRobust U π ∧
      ∃ ν : MeasureTheory.Measure (XuDRMDP.Finite.Parameters n a), XuDRMDP.Finite.Saddle U π ν :=
  XuT.main_thm U π hπ
