-- Prove2me | solution 1 for StochasticProg.MultistageV2.thm1_finite_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T17:33:00.729501+00:00
-- url     : https://prove2.me/submissions/26d2a55d-e886-4457-bba1-2bfa50047a59

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs
import Definitions.Def_StochasticProg_MultistageV2_Feasible
import Definitions.Def_StochasticProg_MultistageV2_obj
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_Cuts_empty
import Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible
import Definitions.Def_StochasticProg_MultistageV2_NLDSOptimal
import Definitions.Def_StochasticProg_MultistageV2_IsProposal
import Definitions.Def_StochasticProg_MultistageV2_IsInfeasibilityDualVertex
import Definitions.Def_StochasticProg_MultistageV2_feasCut
import Definitions.Def_StochasticProg_MultistageV2_IsOptimalDualVertex
import Definitions.Def_StochasticProg_MultistageV2_optCut
import Definitions.Def_StochasticProg_MultistageV2_Step


set_option autoImplicit false

namespace NLS681

open Matrix

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2

/-- Theorem of alternatives over an arbitrary finite variable type. -/
theorem fm_alt' {σ ι : Type} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ) (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  classical
  let e := Fintype.equivFin σ
  rcases fm_alt _ (fun i k => a i (e.symm k)) b with ⟨x, hx⟩ | ⟨l, h0, h1, h2⟩
  · left
    refine ⟨fun s => x (e s), fun i => ?_⟩
    rw [Fintype.sum_equiv e _ (fun k => a i (e.symm k) * x k) (fun s => by simp)]
    exact hx i
  · right
    exact ⟨l, h0, fun s => by simpa using h1 (e s), h2⟩


section Poly

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]

lemma seg_aux (z w : E) (ε : ℝ) (hε : 0 < ε) : z ∈ openSegment ℝ w (z + ε • (z - w)) := by
  have h1 : (0:ℝ) < 1 + ε := by linarith
  set b : ℝ := 1 / (1 + ε) with hbdef
  have hb : 0 < b := by positivity
  have hb1 : b + b * ε = 1 := by rw [hbdef]; field_simp
  refine ⟨b * ε, b, mul_pos hb hε, hb, by linarith, ?_⟩
  have : (b * ε) • w + b • (z + ε • (z - w)) = (b + b * ε) • z := by module
  rw [this, hb1, one_smul]

/-- A polyhedron has finitely many extreme points. -/
theorem ext_finite (g : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    (Set.extremePoints ℝ {z : E | ∀ i, g i z ≤ b i}).Finite := by
  classical
  have hinj : Set.InjOn (fun z => Finset.univ.filter (fun i => g i z = b i))
      (Set.extremePoints ℝ {z : E | ∀ i, g i z ≤ b i}) := by
    intro z hz w hw hzw
    rw [mem_extremePoints] at hz hw
    by_contra hne
    have hev : ∀ i, ∀ᶠ ε in nhds (0:ℝ), g i (z + ε • (z - w)) ≤ b i := by
      intro i
      have hlin : ∀ ε : ℝ, g i (z + ε • (z - w)) = g i z + ε * (g i z - g i w) := by
        intro ε; simp [map_add, map_smul, map_sub, smul_eq_mul]
      by_cases hi : g i z = b i
      · have hwi : g i w = b i := by
          have := congrArg (fun s => i ∈ s) hzw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
          exact this.1 hi
        exact Filter.Eventually.of_forall (fun ε => by rw [hlin, hi, hwi]; simp)
      · have hlt : g i z < b i := lt_of_le_of_ne (hz.1 i) hi
        have hc : Continuous (fun ε : ℝ => g i z + ε * (g i z - g i w)) := by fun_prop
        have : ∀ᶠ ε in nhds (0:ℝ), g i z + ε * (g i z - g i w) < b i :=
          hc.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
        exact this.mono (fun ε hε => by rw [hlin]; exact hε.le)
    have hev' : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        (∀ i, g i (z + ε • (z - w)) ≤ b i) ∧ ε ∈ Set.Ioi (0:ℝ) :=
      ((Filter.eventually_all.2 hev).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨ε, hεP, hε⟩ := hev'.exists
    have := hz.2 w hw.1 _ hεP (seg_aux z w ε hε)
    exact hne this.1.symm
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

lemma active_of_seg (g : E →ₗ[ℝ] ℝ) (c : ℝ) {z z1 z2 : E} (h1 : g z1 ≤ c) (h2 : g z2 ≤ c)
    (hz : z ∈ openSegment ℝ z1 z2) (hc : g z = c) : g z1 = c ∧ g z2 = c := by
  obtain ⟨a, a', ha, ha', haa, rfl⟩ := hz
  simp only [map_add, map_smul, smul_eq_mul] at hc
  have hcc : a * c + a' * c = c := by rw [← add_mul, haa, one_mul]
  constructor
  · by_contra hne
    have hlt : g z1 < c := lt_of_le_of_ne h1 hne
    linarith [mul_lt_mul_of_pos_left hlt ha, mul_le_mul_of_nonneg_left h2 ha'.le]
  · by_contra hne
    have hlt : g z2 < c := lt_of_le_of_ne h2 hne
    linarith [mul_lt_mul_of_pos_left hlt ha', mul_le_mul_of_nonneg_left h1 ha.le]

/-- A nonempty polyhedron without lines has an extreme point. -/
theorem ext_nonempty (g : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (hne : ∃ z, ∀ i, g i z ≤ b i) (hpt : ∀ d, (∀ i, g i d = 0) → d = 0) :
    ∃ z, z ∈ Set.extremePoints ℝ {z : E | ∀ i, g i z ≤ b i} := by
  classical
  let A : E → Finset ι := fun z => Finset.univ.filter (fun i => g i z = b i)
  let Q : ℕ → Prop := fun k => ∃ z, (∀ i, g i z ≤ b i) ∧ (A z).card = k
  obtain ⟨z0, hz0⟩ := hne
  have hle0 : (A z0).card ≤ Fintype.card ι := Finset.card_le_univ _
  obtain ⟨z, hzP, hzc⟩ := Nat.findGreatest_spec (P := Q) hle0 ⟨z0, hz0, rfl⟩
  have hmax : ∀ w, (∀ i, g i w ≤ b i) → (A w).card ≤ (A z).card := by
    intro w hw
    rw [hzc]
    exact Nat.le_findGreatest (Finset.card_le_univ _) ⟨w, hw, rfl⟩
  have key : ∀ z1, (∀ i, g i z1 ≤ b i) → ∀ z2, (∀ i, g i z2 ≤ b i) →
      z ∈ openSegment ℝ z1 z2 → z1 = z := by
    intro z1 h1 z2 h2 hseg
    by_contra hne
    have hact : ∀ i, g i z = b i → g i (z1 - z) = 0 := by
      intro i hi
      have := (active_of_seg (g i) (b i) (h1 i) (h2 i) hseg hi).1
      rw [map_sub, this, hi, sub_self]
    have hd : z1 - z ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨i0, hi0⟩ : ∃ i, g i (z1 - z) ≠ 0 := by
      by_contra hc; push Not at hc; exact hd (hpt _ hc)
    obtain ⟨d, hdact, hdpos⟩ : ∃ d : E, (∀ i, g i z = b i → g i d = 0) ∧ ∃ i, 0 < g i d := by
      rcases lt_or_gt_of_ne hi0 with h | h
      · refine ⟨-(z1 - z), fun i hi => by rw [map_neg, hact i hi, neg_zero], i0, ?_⟩
        rw [map_neg]; linarith
      · exact ⟨z1 - z, hact, i0, h⟩
    let pos := Finset.univ.filter (fun i => 0 < g i d)
    have hpos : pos.Nonempty := by
      obtain ⟨i, hi⟩ := hdpos; exact ⟨i, by simp [pos, hi]⟩
    let r : ι → ℝ := fun i => (b i - g i z) / g i d
    obtain ⟨istar, hist, hteq⟩ := Finset.exists_mem_eq_inf' hpos r
    set t := pos.inf' hpos r with ht
    have hgp : ∀ i ∈ pos, 0 < g i d := fun i hi => by simpa [pos] using hi
    have ht0 : 0 ≤ t := by
      rw [ht]; refine (Finset.le_inf'_iff hpos r).2 (fun i hi => ?_)
      exact div_nonneg (by linarith [hzP i]) (hgp i hi).le
    have hz' : ∀ i, g i (z + t • d) ≤ b i := by
      intro i
      rw [map_add, map_smul, smul_eq_mul]
      by_cases hi : i ∈ pos
      · have : t ≤ r i := Finset.inf'_le r hi
        have hgi := hgp i hi
        have : t * g i d ≤ b i - g i z := by
          have := mul_le_mul_of_nonneg_right this hgi.le
          rwa [div_mul_cancel₀ _ hgi.ne'] at this
        linarith
      · have : g i d ≤ 0 := by simpa [pos] using hi
        nlinarith [hzP i]
    have hsub : A z ⊂ A (z + t • d) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨istar, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, map_add, map_smul,
            smul_eq_mul]
          rw [hteq]
          have hgi := hgp istar hist
          simp only [r]; field_simp; ring
        · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hc
          have := hdact istar hc
          linarith [hgp istar hist]
      · intro i hi
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, map_add, map_smul,
          smul_eq_mul] at hi ⊢
        rw [hdact i hi, hi]; ring
    have := Finset.card_lt_card hsub
    have := hmax _ hz'
    omega
  refine ⟨z, ?_⟩
  rw [mem_extremePoints]
  refine ⟨hzP, fun z1 h1 z2 h2 hseg => ⟨key z1 h1 z2 h2 hseg, ?_⟩⟩
  exact key z2 h2 z1 h1 (openSegment_symm ℝ z1 z2 ▸ hseg)

/-- Extreme point of a polyhedron attaining an attained upper bound of a linear functional. -/
theorem ext_max (g : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (f : E →ₗ[ℝ] ℝ) (M : ℝ)
    (hM : ∀ z, (∀ i, g i z ≤ b i) → f z ≤ M) (hz0 : ∃ z, (∀ i, g i z ≤ b i) ∧ M ≤ f z)
    (hpt : ∀ d, (∀ i, g i d = 0) → d = 0) :
    ∃ z, z ∈ Set.extremePoints ℝ {z : E | ∀ i, g i z ≤ b i} ∧ M ≤ f z := by
  classical
  let g' : Option ι → E →ₗ[ℝ] ℝ := fun o => o.elim (-f) g
  let b' : Option ι → ℝ := fun o => o.elim (-M) b
  have hset : ∀ z, (∀ o, g' o z ≤ b' o) ↔ (∀ i, g i z ≤ b i) ∧ M ≤ f z := by
    intro z
    constructor
    · intro h
      refine ⟨fun i => h (some i), ?_⟩
      have := h none
      simp only [g', b', Option.elim, LinearMap.neg_apply] at this
      linarith
    · rintro ⟨h1, h2⟩ o
      cases o with
      | none => simp only [g', b', Option.elim, LinearMap.neg_apply]; linarith
      | some i => exact h1 i
  obtain ⟨z, hz⟩ := ext_nonempty g' b' (by
      obtain ⟨z, hz⟩ := hz0; exact ⟨z, (hset z).2 hz⟩)
    (fun d hd => hpt d (fun i => hd (some i)))
  rw [mem_extremePoints] at hz
  have hzP := (hset z).1 hz.1
  refine ⟨z, ?_, hzP.2⟩
  rw [mem_extremePoints]
  refine ⟨hzP.1, fun z1 h1 z2 h2 hseg => ?_⟩
  have hfz : f z = M := le_antisymm (hM z hzP.1) hzP.2
  have hh := active_of_seg f M (hM z1 h1) (hM z2 h2) hseg hfz
  exact hz.2 z1 ((hset z1).2 ⟨h1, hh.1.ge⟩) z2 ((hset z2).2 ⟨h2, hh.2.ge⟩) hseg

end Poly

end NLS681

namespace NLS681

open Matrix

section Gen

variable {m n : ℕ}

def mkL {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : ℝ) x, f (c • x) = c * f x) :
    E →ₗ[ℝ] ℝ :=
  { toFun := f, map_add' := hadd, map_smul' := hsmul }

@[simp] lemma mkL_apply {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) (h1 h2) (x : E) :
    mkL f h1 h2 x = f x := rfl

/-- generic NLDS feasibility -/
def PF (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ))
    (x : Fin n → ℝ) (θ : ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ W.mulVec x = b ∧ (∀ q ∈ S, q.2 ≤ q.1 ⬝ᵥ x) ∧
    (∀ q ∈ S', q.2 ≤ q.1 ⬝ᵥ x + θ) ∧ (S' = ∅ → θ = 0)

def PinfSet (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ)) :
    Set ((Fin m → ℝ) × (S → ℝ)) :=
  {z | (∀ i, ∑ r, z.1 r * W r i + ∑ q, z.2 q * (q.1.1 i) ≤ 0) ∧
    (∀ r, -1 ≤ z.1 r ∧ z.1 r ≤ 1) ∧ (∀ q, 0 ≤ z.2 q ∧ z.2 q ≤ 1)}

def PoptSet (W : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    Set ((Fin m → ℝ) × (S → ℝ) × (S' → ℝ)) :=
  {z | (∀ q, 0 ≤ z.2.1 q) ∧ (∀ q, 0 ≤ z.2.2 q) ∧
    (∀ i, ∑ r, z.1 r * W r i + ∑ q, z.2.1 q * (q.1.1 i) + ∑ q, z.2.2 q * (q.1.1 i) ≤ c i) ∧
    (S'.Nonempty → ∑ q, z.2.2 q = 1)}

noncomputable def ginf (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ)) :
    (Fin n ⊕ ((Fin m ⊕ Fin m) ⊕ (S ⊕ S))) → ((Fin m → ℝ) × (S → ℝ)) →ₗ[ℝ] ℝ :=
  Sum.elim
    (fun i => mkL (fun z => ∑ r, z.1 r * W r i + ∑ q, z.2 q * (q.1.1 i))
      (by intro x y; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
            Finset.sum_add_distrib]; ring)
      (by intro c x; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            mul_assoc, ← Finset.mul_sum]; ring))
    (Sum.elim
      (Sum.elim (fun r => mkL (fun z => -z.1 r) (by intro x y; simp; ring) (by intro c x; simp))
        (fun r => mkL (fun z => z.1 r) (by intro x y; simp) (by intro c x; simp)))
      (Sum.elim (fun q => mkL (fun z => -z.2 q) (by intro x y; simp; ring) (by intro c x; simp))
        (fun q => mkL (fun z => z.2 q) (by intro x y; simp) (by intro c x; simp))))

def binf (m n : ℕ) (S : Finset ((Fin n → ℝ) × ℝ)) : (Fin n ⊕ ((Fin m ⊕ Fin m) ⊕ (S ⊕ S))) → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (Sum.elim (fun _ => 1) (fun _ => 1))
    (Sum.elim (fun _ => 0) (fun _ => 1)))

lemma pinf_eq (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ)) :
    PinfSet W S = {z | ∀ i, ginf W S i z ≤ binf m n S i} := by
  ext z
  simp only [PinfSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    rcases i with i | ((r | r) | (q | q))
    · simpa [ginf, binf] using h1 i
    · simp [ginf, binf]; linarith [(h2 r).1]
    · simpa [ginf, binf] using (h2 r).2
    · simp [ginf, binf]; linarith [(h3 q).1]
    · simpa [ginf, binf] using (h3 q).2
  · intro h
    refine ⟨fun i => by simpa [ginf, binf] using h (Sum.inl i), fun r => ⟨?_, ?_⟩, fun q => ⟨?_, ?_⟩⟩
    · have := h (Sum.inr (Sum.inl (Sum.inl r))); simp [ginf, binf] at this; linarith
    · simpa [ginf, binf] using h (Sum.inr (Sum.inl (Sum.inr r)))
    · have := h (Sum.inr (Sum.inr (Sum.inl q))); simp [ginf, binf] at this; linarith
    · simpa [ginf, binf] using h (Sum.inr (Sum.inr (Sum.inr q)))

lemma pinf_pt (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ))
    (d : (Fin m → ℝ) × (S → ℝ)) (hd : ∀ i, ginf W S i d = 0) : d = 0 := by
  have h1 : ∀ r, d.1 r = 0 := fun r => by simpa [ginf] using hd (Sum.inr (Sum.inl (Sum.inr r)))
  have h2 : ∀ q, d.2 q = 0 := fun q => by simpa [ginf] using hd (Sum.inr (Sum.inr (Sum.inr q)))
  exact Prod.ext (funext h1) (funext h2)

noncomputable def gopt (W : Matrix (Fin m) (Fin n) ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    (S ⊕ (S' ⊕ (Fin n ⊕ Bool))) → ((Fin m → ℝ) × (S → ℝ) × (S' → ℝ)) →ₗ[ℝ] ℝ :=
  Sum.elim (fun q => mkL (fun z => -z.2.1 q) (by intro x y; simp; ring) (by intro c x; simp))
    (Sum.elim (fun q => mkL (fun z => -z.2.2 q) (by intro x y; simp; ring) (by intro c x; simp))
      (Sum.elim
        (fun i => mkL (fun z => ∑ r, z.1 r * W r i + ∑ q, z.2.1 q * (q.1.1 i) +
            ∑ q, z.2.2 q * (q.1.1 i))
          (by intro x y; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
                Finset.sum_add_distrib]; ring)
          (by intro c x; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
                mul_assoc, ← Finset.mul_sum]; ring))
        (fun t => mkL (fun z => (if t then (1:ℝ) else -1) * ((if S'.Nonempty then (1:ℝ) else 0) *
            ∑ q, z.2.2 q))
          (by intro x y; simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]; ring)
          (by intro c x; simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
                ← Finset.mul_sum]; ring))))

noncomputable def bopt (c : Fin n → ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    (S ⊕ (S' ⊕ (Fin n ⊕ Bool))) → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim c
    (fun t => (if t then (1:ℝ) else -1) * (if S'.Nonempty then (1:ℝ) else 0))))

lemma popt_eq (W : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    PoptSet W c S S' = {z | ∀ i, gopt W S S' i z ≤ bopt c S S' i} := by
  ext z
  simp only [PoptSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i
    rcases i with q | (q | (i | t))
    · simpa [gopt, bopt] using h1 q
    · simpa [gopt, bopt] using h2 q
    · simpa [gopt, bopt] using h3 i
    · by_cases hne : S'.Nonempty
      · have hs := h4 hne
        cases t <;> simp only [gopt, bopt, Sum.elim_inr, mkL_apply, if_pos hne, hs] <;> norm_num
      · cases t <;> simp [gopt, bopt, hne]
  · intro h
    refine ⟨fun q => by simpa [gopt, bopt] using h (Sum.inl q),
      fun q => by simpa [gopt, bopt] using h (Sum.inr (Sum.inl q)),
      fun i => by simpa [gopt, bopt] using h (Sum.inr (Sum.inr (Sum.inl i))), fun hne => ?_⟩
    have h1 := h (Sum.inr (Sum.inr (Sum.inr true)))
    have h2 := h (Sum.inr (Sum.inr (Sum.inr false)))
    simp only [gopt, bopt, Sum.elim_inr, mkL_apply, if_pos hne] at h1 h2
    norm_num at h1 h2
    rw [Finset.univ_eq_attach]
    linarith

lemma popt_pt (W : Matrix (Fin m) (Fin n) ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ))
    (hli : LinearIndependent ℝ (fun r : Fin m => W r))
    (d : (Fin m → ℝ) × (S → ℝ) × (S' → ℝ)) (hd : ∀ i, gopt W S S' i d = 0) : d = 0 := by
  have h1 : ∀ q, d.2.1 q = 0 := fun q => by simpa [gopt] using hd (Sum.inl q)
  have h2 : ∀ q, d.2.2 q = 0 := fun q => by simpa [gopt] using hd (Sum.inr (Sum.inl q))
  have h3 : ∀ i, ∑ r, d.1 r * W r i = 0 := by
    intro i
    have := hd (Sum.inr (Sum.inr (Sum.inl i)))
    simpa [gopt, h1, h2] using this
  have h4 : ∑ r, d.1 r • W r = 0 := by
    funext i
    simpa [Finset.sum_apply] using h3 i
  have h5 := Fintype.linearIndependent_iff.1 hli d.1 h4
  exact Prod.ext (funext h5) (Prod.ext (funext h1) (funext h2))

noncomputable def finfL (b : Fin m → ℝ) (S : Finset ((Fin n → ℝ) × ℝ)) :
    ((Fin m → ℝ) × (S → ℝ)) →ₗ[ℝ] ℝ :=
  mkL (fun z => z.1 ⬝ᵥ b + ∑ q, z.2 q * q.1.2)
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]; ring)
    (by intro c x; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, Pi.smul_apply,
          smul_eq_mul, mul_assoc, ← Finset.mul_sum]; ring)

noncomputable def foptL (b : Fin m → ℝ) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    ((Fin m → ℝ) × (S → ℝ) × (S' → ℝ)) →ₗ[ℝ] ℝ :=
  mkL (fun z => z.1 ⬝ᵥ b + ∑ q, z.2.1 q * q.1.2 + ∑ q, z.2.2 q * q.1.2)
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, Pi.add_apply, add_mul,
          Finset.sum_add_distrib]; ring)
    (by intro c x; simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, Pi.smul_apply,
          smul_eq_mul, mul_assoc, ← Finset.mul_sum]; ring)

/-- weak duality -/
lemma wd (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ)) {z : (Fin m → ℝ) × (S → ℝ) × (S' → ℝ)}
    (hz : z ∈ PoptSet W c S S') {x : Fin n → ℝ} {θ : ℝ} (hx : PF W b S S' x θ) :
    z.1 ⬝ᵥ b + ∑ q, z.2.1 q * q.1.2 + ∑ q, z.2.2 q * q.1.2 ≤ c ⬝ᵥ x + θ := by
  obtain ⟨hρ, hσ, hrow, hsum⟩ := hz
  obtain ⟨hx0, hWx, hS, hS', hemp⟩ := hx
  have e1 : z.1 ⬝ᵥ b = ∑ i, x i * ∑ r, z.1 r * W r i := by
    rw [← hWx]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have e2 : ∑ q, z.2.1 q * q.1.2 ≤ ∑ i, x i * ∑ q, z.2.1 q * q.1.1 i := by
    calc ∑ q, z.2.1 q * q.1.2 ≤ ∑ q : S, z.2.1 q * (q.1.1 ⬝ᵥ x) :=
          Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hS q.1 q.2) (hρ q))
      _ = _ := by
          simp only [dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have e3 : ∑ q, z.2.2 q * q.1.2 ≤ ∑ i, x i * ∑ q, z.2.2 q * q.1.1 i + θ := by
    have h3 : ∑ q, z.2.2 q * q.1.2 ≤ ∑ q : S', z.2.2 q * (q.1.1 ⬝ᵥ x + θ) :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hS' q.1 q.2) (hσ q))
    have h4 : ∑ q : S', z.2.2 q * (q.1.1 ⬝ᵥ x + θ) =
        ∑ i, x i * ∑ q, z.2.2 q * q.1.1 i + θ * ∑ q, z.2.2 q := by
      simp only [mul_add, Finset.sum_add_distrib, dotProduct, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      · exact Finset.sum_congr rfl (fun _ _ => by ring)
    have h5 : θ * ∑ q, z.2.2 q = θ := by
      by_cases hne : S'.Nonempty
      · rw [hsum hne, mul_one]
      · rw [hemp (Finset.not_nonempty_iff_eq_empty.1 hne), zero_mul]
    linarith
  have e4 : ∑ i, x i * (∑ r, z.1 r * W r i + ∑ q, z.2.1 q * q.1.1 i +
      ∑ q, z.2.2 q * q.1.1 i) ≤ c ⬝ᵥ x := by
    simp only [dotProduct]
    exact Finset.sum_le_sum (fun i _ => by
      rw [mul_comm (c i)]; exact mul_le_mul_of_nonneg_left (hrow i) (hx0 i))
  have e5 : ∑ i, x i * (∑ r, z.1 r * W r i + ∑ q, z.2.1 q * q.1.1 i +
      ∑ q, z.2.2 q * q.1.1 i) = ∑ i, x i * ∑ r, z.1 r * W r i +
      ∑ i, x i * ∑ q, z.2.1 q * q.1.1 i + ∑ i, x i * ∑ q, z.2.2 q * q.1.1 i := by
    simp only [mul_add, Finset.sum_add_distrib]
  linarith

end Gen

end NLS681

namespace NLS681

open Matrix

section Gen2

variable {m n : ℕ}

/-- strong duality: an optimal primal value is matched by a dual feasible point -/
theorem sd (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ)) (xs : Fin n → ℝ) (θs : ℝ) (hfs : PF W b S S' xs θs)
    (hopt : ∀ x θ, PF W b S S' x θ → c ⬝ᵥ xs + θs ≤ c ⬝ᵥ x + θ) :
    ∃ z ∈ PoptSet W c S S', c ⬝ᵥ xs + θs ≤ foptL b S S' z := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = if S'.Nonempty then 1 else 0 := ⟨_, rfl⟩
  let a : (Fin n ⊕ (S ⊕ (S' ⊕ (Unit ⊕ (Unit ⊕ Unit))))) → (Fin m ⊕ (S ⊕ S')) → ℝ :=
    Sum.elim (fun i => Sum.elim (fun r => W r i) (Sum.elim (fun q => q.1.1 i) (fun q => q.1.1 i)))
    (Sum.elim (fun q => Sum.elim (fun _ => 0)
        (Sum.elim (fun q' => if q' = q then -1 else 0) (fun _ => 0)))
    (Sum.elim (fun q => Sum.elim (fun _ => 0)
        (Sum.elim (fun _ => 0) (fun q' => if q' = q then -1 else 0)))
    (Sum.elim (fun _ => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => s)))
    (Sum.elim (fun _ => Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => -s)))
      (fun _ => Sum.elim (fun r => -b r) (Sum.elim (fun q => -q.1.2) (fun q => -q.1.2)))))))
  let bb : (Fin n ⊕ (S ⊕ (S' ⊕ (Unit ⊕ (Unit ⊕ Unit))))) → ℝ :=
    Sum.elim c (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => s)
      (Sum.elim (fun _ => -s) (fun _ => -(c ⬝ᵥ xs + θs))))))
  rcases fm_alt' a bb with ⟨z, hz⟩ | ⟨l, hl0, hl1, hl2⟩
  · refine ⟨(fun r => z (Sum.inl r), fun q => z (Sum.inr (Sum.inl q)),
      fun q => z (Sum.inr (Sum.inr q))), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q
      have := hz (Sum.inr (Sum.inl q))
      simp [-Finset.univ_eq_attach, a, bb, Fintype.sum_sum_type] at this
      simpa using this
    · intro q
      have := hz (Sum.inr (Sum.inr (Sum.inl q)))
      simp [-Finset.univ_eq_attach, a, bb, Fintype.sum_sum_type] at this
      simpa using this
    · intro i
      have := hz (Sum.inl i)
      simp only [a, bb, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at this
      simp only
      have e1 : ∑ r, z (Sum.inl r) * W r i = ∑ r, W r i * z (Sum.inl r) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      have e2 : ∑ q : S, z (Sum.inr (Sum.inl q)) * q.1.1 i = ∑ q : S, q.1.1 i * z (Sum.inr (Sum.inl q)) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      have e3 : ∑ q : S', z (Sum.inr (Sum.inr q)) * q.1.1 i =
          ∑ q : S', q.1.1 i * z (Sum.inr (Sum.inr q)) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [e1, e2, e3]; linarith
    · intro hne
      have h1 := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
      have h2 := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
      rw [if_pos hne] at hs
      simp [a, bb, Fintype.sum_sum_type, hs, Finset.sum_neg_distrib] at h1 h2
      simp only
      rw [Finset.univ_eq_attach]
      linarith
    · have h := hz (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
      simp only [a, bb, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h
      simp only [foptL, mkL_apply, dotProduct]
      have e1 : ∑ r, -b r * z (Sum.inl r) = -∑ r, z (Sum.inl r) * b r := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ q : S, -q.1.2 * z (Sum.inr (Sum.inl q)) = -∑ q : S, z (Sum.inr (Sum.inl q)) * q.1.2 := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e3 : ∑ q : S', -q.1.2 * z (Sum.inr (Sum.inr q)) =
          -∑ q : S', z (Sum.inr (Sum.inr q)) * q.1.2 := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2, e3] at h
      simp only [dotProduct] at h ⊢
      linarith
  · exfalso
    obtain ⟨lam, hlamd⟩ : ∃ v, v = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))) :=
      ⟨_, rfl⟩
    obtain ⟨gp, hgpd⟩ : ∃ v, v = l (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) := ⟨_, rfl⟩
    obtain ⟨gm, hgmd⟩ : ∃ v, v = l (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) :=
      ⟨_, rfl⟩
    have hlam : 0 ≤ lam := hlamd ▸ hl0 _
    have hW : ∀ r, ∑ i, l (Sum.inl i) * W r i = lam * b r := by
      intro r
      have := hl1 (Sum.inl r)
      simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, Fintype.sum_unique, mul_neg] at this
      rw [← hlamd] at this
      linarith
    have hS : ∀ q : S, lam * q.1.2 ≤ ∑ i, l (Sum.inl i) * q.1.1 i := by
      intro q
      have := hl1 (Sum.inr (Sum.inl q))
      simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, mul_ite, mul_neg, mul_one,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Fintype.sum_unique] at this
      rw [← hlamd] at this
      have := hl0 (Sum.inr (Sum.inl q))
      linarith
    have hS' : ∀ q : S', lam * q.1.2 ≤ ∑ i, l (Sum.inl i) * q.1.1 i + s * (gp - gm) := by
      intro q
      have := hl1 (Sum.inr (Sum.inr q))
      simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, mul_ite, mul_neg, mul_one,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Fintype.sum_unique] at this
      rw [← hlamd, ← hgpd, ← hgmd] at this
      have := hl0 (Sum.inr (Sum.inr (Sum.inl q)))
      linarith
    have hval : ∑ i, l (Sum.inl i) * c i + s * (gp - gm) < lam * (c ⬝ᵥ xs + θs) := by
      simp only [bb, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
        Finset.sum_const_zero, zero_add, Fintype.sum_unique, mul_neg] at hl2
      rw [← hlamd, ← hgpd, ← hgmd] at hl2
      linarith
    have hth0 : S' = ∅ → s * (gp - gm) = 0 := by
      intro he
      rw [if_neg (by simp [he])] at hs
      rw [hs, zero_mul]
    have hxx : ∀ i, 0 ≤ l (Sum.inl i) := fun i => hl0 _
    obtain ⟨hx0, hWx, hSx, hS'x, hemp⟩ := hfs
    have hl1' : (0:ℝ) < lam + 1 := by linarith
    have hsplit : ∀ w : Fin n → ℝ, ∑ i, w i * ((l (Sum.inl i) + xs i) / (lam + 1)) =
        (∑ i, l (Sum.inl i) * w i + w ⬝ᵥ xs) / (lam + 1) := by
      intro w
      simp only [dotProduct]
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hPF : PF W b S S' (fun i => (l (Sum.inl i) + xs i) / (lam + 1)) ((s * (gp - gm) + θs) / (lam + 1)) := by
      refine ⟨fun i => div_nonneg (add_nonneg (hxx i) (hx0 i)) hl1'.le, ?_, ?_, ?_, ?_⟩
      · funext r
        have h2 : W r ⬝ᵥ xs = b r := congrFun hWx r
        have h3 := hsplit (W r)
        simp only [Matrix.mulVec, dotProduct] at h3 ⊢
        simp only [dotProduct] at h2
        rw [h3, hW r, h2]
        field_simp
      · intro q hq
        have h1 := hS ⟨q, hq⟩
        have h2 := hSx q hq
        simp only [dotProduct] at h2 ⊢
        have h3 := hsplit q.1
        simp only [dotProduct] at h3
        rw [h3, le_div_iff₀ hl1']
        simp only at h1
        nlinarith
      · intro q hq
        have h1 := hS' ⟨q, hq⟩
        have h2 := hS'x q hq
        simp only [dotProduct] at h2 ⊢
        have h3 := hsplit q.1
        simp only [dotProduct] at h3
        rw [h3, ← add_div, le_div_iff₀ hl1']
        simp only at h1
        nlinarith
      · intro he
        rw [hth0 he, hemp he]; simp
    have h1 := hopt _ _ hPF
    have h3 := hsplit c
    simp only [dotProduct] at h3 h1 hval
    rw [h3, ← add_div, le_div_iff₀ hl1'] at h1
    nlinarith

end Gen2

end NLS681

namespace NLS681

open Matrix

section Gen3

variable {m n : ℕ}

/-- Farkas for an infeasible NLDS: a box-normalised dual ray. -/
theorem farkas_inf (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ)) (hinf : ¬ ∃ x θ, PF W b S S' x θ) :
    ∃ z ∈ PinfSet W S, 0 < finfL b S z := by
  classical
  let a : (Fin n ⊕ (Fin m ⊕ (Fin m ⊕ S))) → Fin n → ℝ :=
    Sum.elim (fun i j => if j = i then -1 else 0)
      (Sum.elim (fun r j => W r j) (Sum.elim (fun r j => -W r j) (fun q j => -q.1.1 j)))
  let bb : (Fin n ⊕ (Fin m ⊕ (Fin m ⊕ S))) → ℝ :=
    Sum.elim (fun _ => 0) (Sum.elim b (Sum.elim (fun r => -b r) (fun q => -q.1.2)))
  rcases fm_alt' a bb with ⟨x, hx⟩ | ⟨l, hl0, hl1, hl2⟩
  · exfalso
    apply hinf
    refine ⟨x, if S' = ∅ then 0 else ∑ q ∈ S', |q.2 - q.1 ⬝ᵥ x|, fun i => ?_, ?_, fun q hq => ?_,
      fun q hq => ?_, fun he => by rw [if_pos he]⟩
    · have := hx (Sum.inl i); simp [-Finset.univ_eq_attach, a, bb] at this; linarith
    · funext r
      have h1 := hx (Sum.inr (Sum.inl r))
      have h2 := hx (Sum.inr (Sum.inr (Sum.inl r)))
      simp [-Finset.univ_eq_attach, a, bb] at h1 h2
      simp only [Matrix.mulVec, dotProduct]
      linarith
    · have := hx (Sum.inr (Sum.inr (Sum.inr ⟨q, hq⟩)))
      simp [-Finset.univ_eq_attach, a, bb] at this
      simp only [dotProduct]
      linarith
    · have hne : S' ≠ ∅ := Finset.ne_empty_of_mem hq
      rw [if_neg hne]
      have h1 : q.2 - q.1 ⬝ᵥ x ≤ ∑ q ∈ S', |q.2 - q.1 ⬝ᵥ x| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun q => |q.2 - q.1 ⬝ᵥ x|)
          (fun _ _ => abs_nonneg _) hq)
      linarith
  · -- dual ray
    let π : Fin m → ℝ := fun r => l (Sum.inr (Sum.inr (Sum.inl r))) - l (Sum.inr (Sum.inl r))
    let ρ : S → ℝ := fun q => l (Sum.inr (Sum.inr (Sum.inr q)))
    have hrow : ∀ i, ∑ r, π r * W r i + ∑ q, ρ q * q.1.1 i ≤ 0 := by
      intro i
      have := hl1 i
      simp [-Finset.univ_eq_attach, a, Fintype.sum_sum_type] at this
      simp only [π, ρ, sub_mul, Finset.sum_sub_distrib]
      have := hl0 (Sum.inl i)
      linarith
    have hobj : 0 < π ⬝ᵥ b + ∑ q, ρ q * q.1.2 := by
      simp [-Finset.univ_eq_attach, bb, Fintype.sum_sum_type] at hl2
      simp only [π, ρ, dotProduct, sub_mul, Finset.sum_sub_distrib]
      linarith
    have hρ0 : ∀ q, 0 ≤ ρ q := fun q => hl0 _
    set K : ℝ := 1 + ∑ r, |π r| + ∑ q, ρ q with hK
    have hK1 : ∀ r, |π r| ≤ K := by
      intro r
      have := Finset.single_le_sum (f := fun r => |π r|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ r)
      have := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hρ0 q)
      linarith
    have hK2 : ∀ q, ρ q ≤ K := by
      intro q
      have := Finset.single_le_sum (f := fun q => ρ q) (fun q _ => hρ0 q) (Finset.mem_univ q)
      have := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => abs_nonneg (π r))
      linarith
    have hKpos : 0 < K := by
      have := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => abs_nonneg (π r))
      have := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hρ0 q)
      linarith
    refine ⟨(fun r => π r / K, fun q => ρ q / K), ⟨fun i => ?_, fun r => ⟨?_, ?_⟩,
      fun q => ⟨div_nonneg (hρ0 q) hKpos.le, (div_le_one hKpos).2 (hK2 q)⟩⟩, ?_⟩
    · have e : ∑ r, π r / K * W r i + ∑ q, ρ q / K * q.1.1 i =
          (∑ r, π r * W r i + ∑ q, ρ q * q.1.1 i) / K := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => by ring)
      simp only
      rw [e]
      exact div_nonpos_of_nonpos_of_nonneg (hrow i) hKpos.le
    · simp only
      rw [le_div_iff₀ hKpos]
      have := neg_abs_le (π r); have := hK1 r; linarith
    · simp only
      rw [div_le_one hKpos]
      exact (le_abs_self _).trans (hK1 r)
    · have e : finfL b S (fun r => π r / K, fun q => ρ q / K) =
          (π ⬝ᵥ b + ∑ q, ρ q * q.1.2) / K := by
        simp only [finfL, mkL_apply, dotProduct]
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e]
      exact div_pos hobj hKpos

lemma pinf_compact (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ)) :
    IsCompact (PinfSet W S) := by
  have hcl : IsClosed (PinfSet W S) := by
    rw [pinf_eq, Set.ofPred_forall]
    exact isClosed_iInter (fun i =>
      isClosed_le (ginf W S i).continuous_of_finiteDimensional continuous_const)
  have hbd : Bornology.IsBounded (PinfSet W S) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun z hz => ?_⟩
    obtain ⟨_, h2, h3⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    constructor
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro r; rw [Real.norm_eq_abs, abs_le]; exact h2 r
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro q; rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(h3 q).1], (h3 q).2⟩
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

/-- L4 generic: an infeasible NLDS has an infeasibility dual vertex. -/
theorem l4gen (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ)) (hinf : ¬ ∃ x θ, PF W b S S' x θ) :
    ∃ z ∈ Set.extremePoints ℝ (PinfSet W S), 0 < finfL b S z := by
  obtain ⟨z0, hz0, hpos⟩ := farkas_inf W b S S' hinf
  obtain ⟨zm, hzm, hmax⟩ := (pinf_compact W S).exists_isMaxOn ⟨z0, hz0⟩
    (finfL b S).continuous_of_finiteDimensional.continuousOn
  have hM : ∀ z, (∀ i, ginf W S i z ≤ binf m n S i) → finfL b S z ≤ finfL b S zm := by
    intro z hz
    have hz' : z ∈ PinfSet W S := by rw [pinf_eq]; exact hz
    exact isMaxOn_iff.1 hmax z hz'
  have hzm' : ∀ i, ginf W S i zm ≤ binf m n S i := by
    have := hzm; rw [pinf_eq] at this; exact this
  obtain ⟨z, hz, hfz⟩ := ext_max (ginf W S) (binf m n S) (finfL b S) (finfL b S zm) hM
    ⟨zm, hzm', le_rfl⟩ (pinf_pt W S)
  refine ⟨z, by rw [pinf_eq]; exact hz, ?_⟩
  have := isMaxOn_iff.1 hmax z0 hz0
  linarith

/-- primal optimum exists for a feasible, bounded NLDS -/
theorem primal_opt (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ))
    (hb : ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → W.mulVec x = b → ∀ i, x i ≤ u i)
    (hfeas : ∃ x θ, PF W b S S' x θ) :
    ∃ x θ, PF W b S S' x θ ∧ ∀ x' θ', PF W b S S' x' θ' → c ⬝ᵥ x + θ ≤ c ⬝ᵥ x' + θ' := by
  classical
  obtain ⟨u, hu⟩ := hb
  obtain ⟨x0, θ0, h0⟩ := hfeas
  let X : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ W.mulVec x = b ∧ ∀ q ∈ S, q.2 ≤ q.1 ⬝ᵥ x}
  have hX : IsCompact X := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have e : X = (⋂ i, {x : Fin n → ℝ | 0 ≤ x i}) ∩ ({x | W.mulVec x = b} ∩
          ⋂ q ∈ S, {x : Fin n → ℝ | q.2 ≤ q.1 ⬝ᵥ x}) := by
        ext x; simp [X]
      rw [e]
      exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
        ((isClosed_eq (Continuous.matrix_mulVec continuous_const continuous_id) continuous_const).inter
          (isClosed_biInter fun q _ => isClosed_le continuous_const
            (continuous_const.dotProduct continuous_id)))
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨∑ i, |u i|, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right,
        pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
      exact (hu x hx.1 hx.2.1 i).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |u j|) (fun j _ => abs_nonneg (u j))
          (Finset.mem_univ i)))
  have hx0 : x0 ∈ X := ⟨h0.1, h0.2.1, h0.2.2.1⟩
  by_cases hne : S'.Nonempty
  · let φ : (Fin n → ℝ) → ℝ := fun x => c ⬝ᵥ x + S'.sup' hne (fun q => q.2 - q.1 ⬝ᵥ x)
    have hφ : Continuous φ := by
      refine (continuous_const.dotProduct continuous_id).add ?_
      exact Continuous.finset_sup'_apply hne
        (fun q _ => continuous_const.sub (continuous_const.dotProduct continuous_id))
    obtain ⟨xs, hxs, hmin⟩ := hX.exists_isMinOn ⟨x0, hx0⟩ hφ.continuousOn
    refine ⟨xs, S'.sup' hne (fun q => q.2 - q.1 ⬝ᵥ xs),
      ⟨hxs.1, hxs.2.1, hxs.2.2, fun q hq => ?_, fun h => absurd h hne.ne_empty⟩,
      fun x' θ' h' => ?_⟩
    · have := Finset.le_sup' (fun q => q.2 - q.1 ⬝ᵥ xs) hq
      linarith
    · have hx' : x' ∈ X := ⟨h'.1, h'.2.1, h'.2.2.1⟩
      have h1 : φ xs ≤ φ x' := isMinOn_iff.1 hmin x' hx'
      have h2 : S'.sup' hne (fun q => q.2 - q.1 ⬝ᵥ x') ≤ θ' :=
        Finset.sup'_le hne _ (fun q hq => by have := h'.2.2.2.1 q hq; linarith)
      simp only [φ] at h1
      linarith
  · have hS'e : S' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    obtain ⟨xs, hxs, hmin⟩ := hX.exists_isMinOn ⟨x0, hx0⟩
      (continuous_const.dotProduct continuous_id : Continuous fun x : Fin n → ℝ => c ⬝ᵥ x).continuousOn
    refine ⟨xs, 0, ⟨hxs.1, hxs.2.1, hxs.2.2, fun q hq => by simp [hS'e] at hq, fun _ => rfl⟩,
      fun x' θ' h' => ?_⟩
    have := isMinOn_iff.1 hmin x' ⟨h'.1, h'.2.1, h'.2.2.1⟩
    rw [h'.2.2.2.2 hS'e]
    linarith

/-- L5 generic -/
theorem l5gen (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (S S' : Finset ((Fin n → ℝ) × ℝ))
    (hb : ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → W.mulVec x = b → ∀ i, x i ≤ u i)
    (hli : LinearIndependent ℝ (fun r : Fin m => W r))
    (hfeas : ∃ x θ, PF W b S S' x θ) :
    (∃ x θ, PF W b S S' x θ ∧ ∀ x' θ', PF W b S S' x' θ' → c ⬝ᵥ x + θ ≤ c ⬝ᵥ x' + θ') ∧
    ∃ z ∈ Set.extremePoints ℝ (PoptSet W c S S'),
      ∃ x θ, PF W b S S' x θ ∧ c ⬝ᵥ x + θ = foptL b S S' z := by
  obtain ⟨xs, θs, hfs, hopt⟩ := primal_opt W b c S S' hb hfeas
  refine ⟨⟨xs, θs, hfs, hopt⟩, ?_⟩
  obtain ⟨z0, hz0, hv⟩ := sd W b c S S' xs θs hfs hopt
  have hM : ∀ z, (∀ i, gopt W S S' i z ≤ bopt c S S' i) → foptL b S S' z ≤ c ⬝ᵥ xs + θs := by
    intro z hz
    have hz' : z ∈ PoptSet W c S S' := by rw [popt_eq]; exact hz
    exact wd W b c S S' hz' hfs
  have hz0' : ∀ i, gopt W S S' i z0 ≤ bopt c S S' i := by
    have := hz0; rw [popt_eq] at this; exact this
  obtain ⟨z, hz, hfz⟩ := ext_max (gopt W S S') (bopt c S S') (foptL b S S') (c ⬝ᵥ xs + θs) hM
    ⟨z0, hz0', hv⟩ (popt_pt W S S' hli)
  have hz' : z ∈ Set.extremePoints ℝ (PoptSet W c S S') := by rw [popt_eq]; exact hz
  refine ⟨z, hz', xs, θs, hfs, le_antisymm hfz ?_⟩
  exact hM z (by have := hz'.1; rw [popt_eq] at this; exact this)

end Gen3

end NLS681

namespace NLS681

open StochasticProg StochasticProg.MultistageV2 Matrix

variable {H n m : ℕ} {T : Multistage.Tree H}

section Tree

lemma child_spec {j k : T.Node} (hk : k ∈ T.children j) :
    (T.stage k).val = (T.stage j).val + 1 ∧ T.anc k = j := by
  simpa [Multistage.Tree.children] using hk

lemma anc_child {k : T.Node} (hk : (T.stage k).val ≠ 0) : k ∈ T.children (T.anc k) := by
  simp only [Multistage.Tree.children, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
  exact (T.anc_stage k hk).symm

lemma child_ne_root {j k : T.Node} (hk : k ∈ T.children j) : (T.stage k).val ≠ 0 := by
  rw [(child_spec hk).1]; omega

lemma rhs_root (inst : Instance H n m T) (xp : Fin n → ℝ) :
    rhs inst T.root xp = inst.h T.root := by
  simp [rhs, T.root_stage]

lemma rhs_nonroot (inst : Instance H n m T) {k : T.Node} (hk : (T.stage k).val ≠ 0)
    (xp : Fin n → ℝ) : rhs inst k xp = inst.h k - (inst.Tmat k).mulVec xp := by
  simp [rhs, hk]

lemma feas_root (inst : Instance H n m T) (C : Cuts T n) (xp xp' x : Fin n → ℝ) (θ : ℝ) :
    NLDSFeasible inst C T.root xp x θ ↔ NLDSFeasible inst C T.root xp' x θ := by
  simp only [NLDSFeasible, rhs_root]

lemma optl_root (inst : Instance H n m T) (C : Cuts T n) (xp xp' x : Fin n → ℝ) (θ : ℝ) :
    NLDSOptimal inst C T.root xp x θ ↔ NLDSOptimal inst C T.root xp' x θ := by
  simp only [NLDSOptimal, feas_root inst C xp xp']

lemma prop_opt {inst : Instance H n m T} {C : Cuts T n} {j : T.Node} {x : Fin n → ℝ} {θ : ℝ}
    (h : IsProposal inst C j x θ) : ∃ xp, NLDSOptimal inst C j xp x θ := by
  cases h with
  | root x θ h => exact ⟨0, h⟩
  | child j hj xp θp x θ _ h => exact ⟨xp, h⟩

end Tree

section Inst

theorem l4 (inst : Instance H n m T) (C : Cuts T n) (k : T.Node) (xp : Fin n → ℝ)
    (hinf : ¬ ∃ x θ, NLDSFeasible inst C k xp x θ) :
    ∃ π ρ, IsInfeasibilityDualVertex inst C k xp π ρ := by
  obtain ⟨z, hz, hpos⟩ := l4gen (inst.W (T.stage k)) (rhs inst k xp) (C.feas k) (C.opt k) hinf
  exact ⟨z.1, z.2, hz, hpos⟩

theorem l5 (inst : Instance H n m T)
    (hbdd : ∀ (t : Fin H) (b : Fin m → ℝ), ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (inst.W t).mulVec x = b → ∀ i, x i ≤ u i)
    (hrank : ∀ t : Fin H, LinearIndependent ℝ (fun r : Fin m => inst.W t r))
    (C : Cuts T n) (k : T.Node) (xp : Fin n → ℝ)
    (hfeas : ∃ x θ, NLDSFeasible inst C k xp x θ) :
    (∃ x θ, NLDSOptimal inst C k xp x θ) ∧ ∃ π ρ σ, IsOptimalDualVertex inst C k xp π ρ σ := by
  obtain ⟨⟨x, θ, h1, h2⟩, z, hz, x', θ', h3, h4⟩ := l5gen (inst.W (T.stage k)) (rhs inst k xp)
    (inst.c k) (C.feas k) (C.opt k) (hbdd _ _) (hrank _) hfeas
  exact ⟨⟨x, θ, h1, h2⟩, z.1, z.2.1, z.2.2, hz, x', θ', h3, h4⟩

end Inst

section Growth

def tot (C : Cuts T n) : ℕ := ∑ k, ((C.feas k).card + (C.opt k).card)

lemma upd_sub (f : T.Node → Finset ((Fin n → ℝ) × ℝ)) (j : T.Node) (v : (Fin n → ℝ) × ℝ)
    (k : T.Node) : f k ⊆ Function.update f j (insert v (f j)) k := by
  by_cases h : k = j
  · subst h; rw [Function.update_self]; exact Finset.subset_insert _ _
  · rw [Function.update_of_ne h]

lemma upd_card (f : T.Node → Finset ((Fin n → ℝ) × ℝ)) (j : T.Node) (v : (Fin n → ℝ) × ℝ)
    (hv : v ∉ f j) : ∑ k, (f k).card < ∑ k, (Function.update f j (insert v (f j)) k).card := by
  apply Finset.sum_lt_sum
  · intro k _; exact Finset.card_le_card (upd_sub f j v k)
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [Function.update_self]
    exact Finset.card_lt_card (Finset.ssubset_insert hv)

lemma feasCut_viol (inst : Instance H n m T) (C : Cuts T n) (k : T.Node)
    (hk : (T.stage k).val ≠ 0) (xp : Fin n → ℝ) (π : Fin m → ℝ) (ρ : C.feas k → ℝ)
    (hpos : 0 < π ⬝ᵥ rhs inst k xp + ∑ q, ρ q * q.1.2) :
    (feasCut inst C k π ρ).1 ⬝ᵥ xp < (feasCut inst C k π ρ).2 := by
  rw [rhs_nonroot inst hk, dotProduct_sub] at hpos
  have key : (feasCut inst C k π ρ).1 ⬝ᵥ xp = π ⬝ᵥ (inst.Tmat k).mulVec xp := by
    rw [Matrix.dotProduct_mulVec]; rfl
  rw [key]
  simp only [feasCut]
  linarith

theorem l3 (inst : Instance H n m T) (C C' : Cuts T n) (h : Step inst C C') :
    (∀ k, C.feas k ⊆ C'.feas k ∧ C.opt k ⊆ C'.opt k) ∧ tot C < tot C' := by
  cases h with
  | feas k hk xp θp hprop hinf π ρ hdual =>
    have hnot : feasCut inst C k π ρ ∉ C.feas (T.anc k) := by
      intro hin
      obtain ⟨xp', hopt⟩ := prop_opt hprop
      have h1 := hopt.1.2.2.1 _ hin
      have h2 := feasCut_viol inst C k hk xp π ρ hdual.2
      linarith
    refine ⟨fun k' => ⟨upd_sub _ _ _ k', subset_rfl⟩, ?_⟩
    have := upd_card C.feas (T.anc k) _ hnot
    simp only [tot, Finset.sum_add_distrib]
    omega
  | opt j hj xj θj hprop hready π ρ σ hdual hcut =>
    have hnot : optCut inst C j π ρ σ ∉ C.opt j := by
      intro hin
      rcases hcut with he | hlt
      · rw [he] at hin; simp at hin
      · obtain ⟨xp', hopt⟩ := prop_opt hprop
        have h1 := hopt.1.2.2.2.1 _ hin
        linarith
    refine ⟨fun k' => ⟨subset_rfl, upd_sub _ _ _ k'⟩, ?_⟩
    have := upd_card C.opt j _ hnot
    simp only [tot, Finset.sum_add_distrib]
    omega

end Growth

end NLS681

namespace NLS681

open StochasticProg StochasticProg.MultistageV2 Matrix

variable {H n m : ℕ} {T : Multistage.Tree H}

section Univ

def FC (inst : Instance H n m T) (k : T.Node) (S : Finset ((Fin n → ℝ) × ℝ)) :
    Set ((Fin n → ℝ) × ℝ) :=
  (fun z : (Fin m → ℝ) × (S → ℝ) => ((fun i => ∑ r, z.1 r * inst.Tmat k r i),
      z.1 ⬝ᵥ inst.h k + ∑ q, z.2 q * q.1.2)) ''
    Set.extremePoints ℝ (PinfSet (inst.W (T.stage k)) S)

lemma FC_finite (inst : Instance H n m T) (k : T.Node) (S : Finset ((Fin n → ℝ) × ℝ)) :
    (FC inst k S).Finite := by
  unfold FC
  apply Set.Finite.image
  rw [pinf_eq]
  exact ext_finite _ _

def OV (inst : Instance H n m T) (k : T.Node) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    Set ((Fin m → ℝ) × ℝ) :=
  (fun z : (Fin m → ℝ) × (S → ℝ) × (S' → ℝ) => (z.1, ∑ q, z.2.1 q * q.1.2 + ∑ q, z.2.2 q * q.1.2)) ''
    Set.extremePoints ℝ (PoptSet (inst.W (T.stage k)) (inst.c k) S S')

lemma OV_finite (inst : Instance H n m T) (k : T.Node) (S S' : Finset ((Fin n → ℝ) × ℝ)) :
    (OV inst k S S').Finite := by
  unfold OV
  apply Set.Finite.image
  rw [popt_eq]
  exact ext_finite _ _

noncomputable def G (inst : Instance H n m T) (j : T.Node) (w : T.Node → (Fin m → ℝ) × ℝ) :
    (Fin n → ℝ) × ℝ :=
  (fun i => ∑ k ∈ T.children j, (inst.p k / inst.p j) * ∑ r, (w k).1 r * inst.Tmat k r i,
   ∑ k ∈ T.children j, (inst.p k / inst.p j) * ((w k).1 ⬝ᵥ inst.h k + (w k).2))

lemma optCut_eq_G (inst : Instance H n m T) (C : Cuts T n) (j : T.Node)
    (π : T.Node → Fin m → ℝ) (ρ : (k : T.Node) → C.feas k → ℝ) (σ : (k : T.Node) → C.opt k → ℝ) :
    optCut inst C j π ρ σ =
      G inst j (fun k => (π k, ∑ q, ρ k q * q.1.2 + ∑ q, σ k q * q.1.2)) := by
  simp only [optCut, G, add_assoc]

def Ufe (inst : Instance H n m T) (Uf : T.Node → Finset ((Fin n → ℝ) × ℝ)) (j : T.Node) :
    Set ((Fin n → ℝ) × ℝ) :=
  ⋃ k ∈ (T.children j : Set T.Node), ⋃ S ∈ ((Uf k).powerset : Set (Finset ((Fin n → ℝ) × ℝ))),
    FC inst k S

lemma Ufe_finite (inst : Instance H n m T) (Uf : T.Node → Finset ((Fin n → ℝ) × ℝ))
    (j : T.Node) : (Ufe inst Uf j).Finite :=
  (T.children j).finite_toSet.biUnion (fun k _ =>
    (Uf k).powerset.finite_toSet.biUnion (fun S _ => FC_finite inst k S))

open Classical in
def Uop (inst : Instance H n m T) (Uf Uo : T.Node → Finset ((Fin n → ℝ) × ℝ)) (j : T.Node) :
    Set ((Fin n → ℝ) × ℝ) :=
  G inst j '' Set.pi Set.univ (fun k => if k ∈ T.children j then
    ⋃ S ∈ ((Uf k).powerset : Set (Finset ((Fin n → ℝ) × ℝ))),
      ⋃ S' ∈ ((Uo k).powerset : Set (Finset ((Fin n → ℝ) × ℝ))), OV inst k S S'
    else {((0 : Fin m → ℝ), (0 : ℝ))})

lemma Uop_finite (inst : Instance H n m T) (Uf Uo : T.Node → Finset ((Fin n → ℝ) × ℝ))
    (j : T.Node) : (Uop inst Uf Uo j).Finite := by
  classical
  unfold Uop
  apply Set.Finite.image
  apply Set.Finite.pi
  intro k
  split_ifs
  · exact (Uf k).powerset.finite_toSet.biUnion (fun S _ =>
      (Uo k).powerset.finite_toSet.biUnion (fun S' _ => OV_finite inst k S S'))
  · exact Set.finite_singleton _

theorem l2 (inst : Instance H n m T) :
    ∃ Uf Uo : T.Node → Finset ((Fin n → ℝ) × ℝ), ∀ C : Cuts T n,
      Relation.ReflTransGen (Step inst) (Cuts.empty T n) C →
        ∀ k, C.feas k ⊆ Uf k ∧ C.opt k ⊆ Uo k := by
  classical
  have key : ∀ d : ℕ, ∃ Uf Uo : T.Node → Finset ((Fin n → ℝ) × ℝ), ∀ C : Cuts T n,
      Relation.ReflTransGen (Step inst) (Cuts.empty T n) C → ∀ k, H ≤ (T.stage k).val + d →
        C.feas k ⊆ Uf k ∧ C.opt k ⊆ Uo k := by
    intro d
    induction d with
    | zero =>
      refine ⟨fun _ => ∅, fun _ => ∅, fun C _ k hk => ?_⟩
      have := (T.stage k).isLt
      omega
    | succ d ih =>
      obtain ⟨Uf, Uo, hU⟩ := ih
      refine ⟨fun j => if H ≤ (T.stage j).val + d then Uf j else (Ufe_finite inst Uf j).toFinset,
        fun j => if H ≤ (T.stage j).val + d then Uo j else (Uop_finite inst Uf Uo j).toFinset, ?_⟩
      intro C hC
      have hnew : ∀ j, (T.stage j).val + d + 1 = H →
          C.feas j ⊆ (Ufe_finite inst Uf j).toFinset ∧
            C.opt j ⊆ (Uop_finite inst Uf Uo j).toFinset := by
        induction hC with
        | refl => intro j _; simp [Cuts.empty]
        | tail h1 h2 ih2 =>
          rename_i C1 C2
          intro j hj
          cases h2 with
          | feas k hk xp θp hprop hinf π ρ hdual =>
            refine ⟨?_, (ih2 j hj).2⟩
            show Function.update C1.feas (T.anc k)
              (insert (feasCut inst C1 k π ρ) (C1.feas (T.anc k))) j ⊆ _
            by_cases hjk : j = T.anc k
            · subst hjk
              rw [Function.update_self]
              intro q hq
              rw [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · rw [Set.Finite.mem_toFinset]
                have hst : H ≤ (T.stage k).val + d := by
                  have := T.anc_stage k hk; omega
                exact Set.mem_biUnion (Finset.mem_coe.2 (anc_child hk))
                  (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_powerset.2 (hU C1 h1 k hst).1))
                    ⟨(π, ρ), hdual.1, rfl⟩)
              · exact (ih2 _ hj).1 hq
            · rw [Function.update_of_ne hjk]; exact (ih2 j hj).1
          | opt j' hj' xj θj hprop hready π ρ σ hdual hcut =>
            refine ⟨(ih2 j hj).1, ?_⟩
            show Function.update C1.opt j' (insert (optCut inst C1 j' π ρ σ) (C1.opt j')) j ⊆ _
            by_cases hjj : j = j'
            · subst hjj
              rw [Function.update_self]
              intro q hq
              rw [Finset.mem_insert] at hq
              rcases hq with rfl | hq
              · rw [Set.Finite.mem_toFinset, optCut_eq_G]
                refine ⟨fun k => if k ∈ T.children j then
                  (π k, ∑ q, ρ k q * q.1.2 + ∑ q, σ k q * q.1.2) else (0, 0), ?_, ?_⟩
                · intro k _
                  simp only
                  split_ifs with hk
                  · have hst : H ≤ (T.stage k).val + d := by
                      have := (child_spec hk).1; omega
                    exact Set.mem_biUnion
                      (Finset.mem_coe.2 (Finset.mem_powerset.2 (hU C1 h1 k hst).1))
                      (Set.mem_biUnion
                        (Finset.mem_coe.2 (Finset.mem_powerset.2 (hU C1 h1 k hst).2))
                        ⟨(π k, ρ k, σ k), (hdual k hk).1, rfl⟩)
                  · exact Set.mem_singleton _
                · simp only [G, Prod.mk.injEq]
                  constructor
                  · funext i
                    exact Finset.sum_congr rfl (fun k hk => by rw [if_pos hk])
                  · exact Finset.sum_congr rfl (fun k hk => by rw [if_pos hk])
              · exact (ih2 _ hj).2 hq
            · rw [Function.update_of_ne hjj]; exact (ih2 j hj).2
      intro k hk
      by_cases hk' : H ≤ (T.stage k).val + d
      · simp only [if_pos hk']; exact hU C hC k hk'
      · simp only [if_neg hk']; exact hnew k (by omega)
  obtain ⟨Uf, Uo, hU⟩ := key H
  exact ⟨Uf, Uo, fun C hC k => hU C hC k (by omega)⟩

theorem part1 (inst : Instance H n m T) :
    ¬ ∃ s : ℕ → Cuts T n, s 0 = Cuts.empty T n ∧ ∀ i, Step inst (s i) (s (i + 1)) := by
  rintro ⟨s, h0, hs⟩
  obtain ⟨Uf, Uo, hU⟩ := l2 inst
  have hreach : ∀ i, Relation.ReflTransGen (Step inst) (Cuts.empty T n) (s i) := by
    intro i
    induction i with
    | zero => rw [h0]
    | succ i ih => exact ih.tail (hs i)
  have hgrow : ∀ i, i ≤ tot (s i) := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := (l3 inst _ _ (hs i)).2; omega
  have hbound : ∀ i, tot (s i) ≤ ∑ k, ((Uf k).card + (Uo k).card) := by
    intro i
    apply Finset.sum_le_sum
    intro k _
    have := hU _ (hreach i) k
    exact add_le_add (Finset.card_le_card this.1) (Finset.card_le_card this.2)
  have h1 := hgrow (∑ k, ((Uf k).card + (Uo k).card) + 1)
  have h2 := hbound (∑ k, ((Uf k).card + (Uo k).card) + 1)
  omega

end Univ

end NLS681

namespace NLS681

open StochasticProg StochasticProg.MultistageV2 Matrix

lemma wd_inf {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (S : Finset ((Fin n → ℝ) × ℝ))
    {z : (Fin m → ℝ) × (S → ℝ)} (hz : z ∈ PinfSet W S) {x : Fin n → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hS : ∀ q ∈ S, q.2 ≤ q.1 ⬝ᵥ x) : z.1 ⬝ᵥ W.mulVec x + ∑ q, z.2 q * q.1.2 ≤ 0 := by
  obtain ⟨hrow, _, hbox⟩ := hz
  have e1 : z.1 ⬝ᵥ W.mulVec x = ∑ i, x i * ∑ r, z.1 r * W r i := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have e2 : ∑ q, z.2 q * q.1.2 ≤ ∑ i, x i * ∑ q, z.2 q * q.1.1 i := by
    calc ∑ q, z.2 q * q.1.2 ≤ ∑ q : S, z.2 q * (q.1.1 ⬝ᵥ x) :=
          Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hS q.1 q.2) (hbox q).1)
      _ = _ := by
          simp only [dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have e3 : ∑ i, x i * (∑ r, z.1 r * W r i + ∑ q, z.2 q * q.1.1 i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hx0 i) (hrow i))
  have e4 : ∑ i, x i * (∑ r, z.1 r * W r i + ∑ q, z.2 q * q.1.1 i) =
      ∑ i, x i * ∑ r, z.1 r * W r i + ∑ i, x i * ∑ q, z.2 q * q.1.1 i := by
    simp only [mul_add, Finset.sum_add_distrib]
  linarith

variable {H n m : ℕ} {T : Multistage.Tree H}

section Ctg

noncomputable def ctgF (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) : ℕ → T.Node → ℝ
  | 0, _ => 0
  | d + 1, j => ∑ k ∈ T.children j, (inst.p k / inst.p j) * (inst.c k ⬝ᵥ xs k + ctgF inst xs d k)

noncomputable def ctg (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) (j : T.Node) : ℝ :=
  ctgF inst xs (H - 1 - (T.stage j).val) j

lemma ctg_eq (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) (j : T.Node) :
    ctg inst xs j = ∑ k ∈ T.children j, (inst.p k / inst.p j) *
      (inst.c k ⬝ᵥ xs k + ctg inst xs k) := by
  unfold ctg
  rcases hd : H - 1 - (T.stage j).val with _ | d
  · have : T.children j = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have h1 := (child_spec hk).1
      have h2 := (T.stage k).isLt
      omega
    rw [this]
    simp [ctgF]
  · simp only [ctgF]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have h1 := (child_spec hk).1
    have : H - 1 - (T.stage k).val = d := by omega
    rw [this]

lemma ctg_leaf (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) (j : T.Node)
    (hj : T.children j = ∅) : ctg inst xs j = 0 := by
  rw [ctg_eq, hj, Finset.sum_empty]

lemma p_root (inst : Instance H n m T) : inst.p T.root = 1 := by
  have h := inst.hp_sum (T.stage T.root)
  have e : Finset.univ.filter (fun k => T.stage k = T.stage T.root) = {T.root} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk; exact T.root_unique k (by rw [hk]; exact T.root_stage)
    · rintro rfl; rfl
  rw [e, Finset.sum_singleton] at h
  exact h

/-- layering identity: the expected cost equals root cost plus cost-to-go -/
lemma obj_eq (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) :
    obj inst xs = inst.c T.root ⬝ᵥ xs T.root + ctg inst xs T.root := by
  classical
  let B : ℕ → ℝ := fun t => ∑ k ∈ Finset.univ.filter (fun k => (T.stage k).val = t),
    inst.p k * (inst.c k ⬝ᵥ xs k)
  let A : ℕ → ℝ := fun t => ∑ k ∈ Finset.univ.filter (fun k => (T.stage k).val = t),
    inst.p k * ctg inst xs k
  have hstep : ∀ t, A t = B (t + 1) + A (t + 1) := by
    intro t
    simp only [A, B]
    rw [← Finset.sum_add_distrib]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
        (fun k => (T.stage k).val = t + 1)) (t := Finset.univ.filter (fun k => (T.stage k).val = t))
      (g := T.anc) (f := fun k => inst.p k * (inst.c k ⬝ᵥ xs k) + inst.p k * ctg inst xs k)
      (by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        have := T.anc_stage k (by omega)
        omega)
    rw [← hfib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [ctg_eq, Finset.mul_sum]
    have e : (Finset.univ.filter (fun k => (T.stage k).val = t + 1)).filter (fun k => T.anc k = j)
        = T.children j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multistage.Tree.children, hj]
    rw [e]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hpj : inst.p j ≠ 0 := (inst.hp_pos j).ne'
    field_simp
  have hsum : ∀ t, ∑ s ∈ Finset.range (t + 1), B s + A t = B 0 + A 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, add_assoc, ← hstep t]; exact ih
  have hAH : ∀ t, H ≤ t → A t = 0 := by
    intro t ht
    simp only [A]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := (T.stage k).isLt
    omega
  have hBH : ∀ t, H ≤ t → B t = 0 := by
    intro t ht
    simp only [B]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have := (T.stage k).isLt
    omega
  have hH : 0 < H := by have := (T.stage T.root).isLt; omega
  have hA1 : A (H - 1) = 0 := by
    rw [hstep, show H - 1 + 1 = H by omega, hAH H le_rfl, hBH H le_rfl, add_zero]
  have hobj : obj inst xs = ∑ s ∈ Finset.range H, B s := by
    simp only [obj, B]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun k => (T.stage k).val)
      (fun k _ => Finset.mem_range.2 (T.stage k).isLt)]
  have h := hsum (H - 1)
  rw [show H - 1 + 1 = H by omega, hA1, add_zero, ← hobj] at h
  rw [h]
  have hB0 : B 0 = inst.c T.root ⬝ᵥ xs T.root := by
    simp only [B]
    have e : Finset.univ.filter (fun k => (T.stage k).val = 0) = {T.root} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨T.root_unique k, fun hk => hk ▸ T.root_stage⟩
    rw [e, Finset.sum_singleton, p_root, one_mul]
  have hA0 : A 0 = ctg inst xs T.root := by
    simp only [A]
    have e : Finset.univ.filter (fun k => (T.stage k).val = 0) = {T.root} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨T.root_unique k, fun hk => hk ▸ T.root_stage⟩
    rw [e, Finset.sum_singleton, p_root, one_mul]
  rw [hB0, hA0]

end Ctg

section Valid

lemma optCut_eval (inst : Instance H n m T) (C : Cuts T n) (j : T.Node)
    (π : T.Node → Fin m → ℝ) (ρ : (k : T.Node) → C.feas k → ℝ) (σ : (k : T.Node) → C.opt k → ℝ)
    (x : Fin n → ℝ) :
    (optCut inst C j π ρ σ).2 - (optCut inst C j π ρ σ).1 ⬝ᵥ x =
      ∑ k ∈ T.children j, (inst.p k / inst.p j) *
        (π k ⬝ᵥ rhs inst k x + ∑ q, ρ k q * q.1.2 + ∑ q, σ k q * q.1.2) := by
  have h1 : (optCut inst C j π ρ σ).1 ⬝ᵥ x = ∑ k ∈ T.children j,
      (inst.p k / inst.p j) * (π k ⬝ᵥ (inst.Tmat k).mulVec x) := by
    simp only [optCut, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h1]
  simp only [optCut]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [rhs_nonroot inst (child_ne_root hk), dotProduct_sub]
  ring

lemma noch (inst : Instance H n m T) (C : Cuts T n)
    (hC : Relation.ReflTransGen (Step inst) (Cuts.empty T n) C) (j : T.Node)
    (hj : T.children j = ∅) : C.opt j = ∅ := by
  induction hC with
  | refl => rfl
  | tail h1 h2 ih =>
    cases h2 with
    | feas k hk xp θp hprop hinf π ρ hdual => exact ih
    | opt j' hj' xj θj hprop hready π ρ σ hdual hcut =>
      show Function.update _ j' _ j = ∅
      have hne : j ≠ j' := by
        rintro rfl; rw [hj] at hj'; exact Finset.not_nonempty_empty hj'
      rw [Function.update_of_ne hne]; exact ih

/-- L6: cuts are valid for every feasible solution, with the true cost-to-go -/
theorem l6 (inst : Instance H n m T) (C : Cuts T n)
    (hC : Relation.ReflTransGen (Step inst) (Cuts.empty T n) C)
    (xs : T.Node → Fin n → ℝ) (hxs : Feasible inst xs) :
    ∀ j, (∀ q ∈ C.feas j, q.2 ≤ q.1 ⬝ᵥ xs j) ∧
      (∀ q ∈ C.opt j, q.2 ≤ q.1 ⬝ᵥ xs j + ctg inst xs j) := by
  induction hC with
  | refl => intro j; simp [Cuts.empty]
  | tail h1 h2 ih =>
    rename_i C1 C2
    cases h2 with
    | feas k hk xp θp hprop hinf π ρ hdual =>
      intro j
      refine ⟨?_, (ih j).2⟩
      show ∀ q ∈ Function.update C1.feas (T.anc k)
        (insert (feasCut inst C1 k π ρ) (C1.feas (T.anc k))) j, _
      by_cases hjk : j = T.anc k
      · subst hjk
        rw [Function.update_self]
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · have hv := wd_inf (inst.W (T.stage k)) (C1.feas k) hdual.1.1 (hxs k).1 (ih k).1
          dsimp only at hv
          rw [(hxs k).2, rhs_nonroot inst hk, dotProduct_sub] at hv
          have key : (feasCut inst C1 k π ρ).1 ⬝ᵥ xs (T.anc k) =
              π ⬝ᵥ (inst.Tmat k).mulVec (xs (T.anc k)) := by
            rw [Matrix.dotProduct_mulVec]; rfl
          rw [key]
          simp only [feasCut]
          linarith
        · exact (ih _).1 q hq
      · rw [Function.update_of_ne hjk]; exact (ih j).1
    | opt j' hj' xj θj hprop hready π ρ σ hdual hcut =>
      intro j
      refine ⟨(ih j).1, ?_⟩
      show ∀ q ∈ Function.update C1.opt j' (insert (optCut inst C1 j' π ρ σ) (C1.opt j')) j, _
      by_cases hjj : j = j'
      · subst hjj
        rw [Function.update_self]
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · have hev := optCut_eval inst C1 j π ρ σ (xs j)
          suffices hle : ∑ k ∈ T.children j, (inst.p k / inst.p j) *
              (π k ⬝ᵥ rhs inst k (xs j) + ∑ q, ρ k q * q.1.2 + ∑ q, σ k q * q.1.2) ≤
              ctg inst xs j by linarith
          rw [ctg_eq]
          refine Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left ?_
            (div_nonneg (inst.hp_pos k).le (inst.hp_pos j).le))
          have hanc := (child_spec hk).2
          have hPF : PF (inst.W (T.stage k)) (rhs inst k (xs j)) (C1.feas k) (C1.opt k)
              (xs k) (ctg inst xs k) := by
            refine ⟨(hxs k).1, by rw [(hxs k).2, hanc], (ih k).1, (ih k).2, fun he => ?_⟩
            by_cases hch : (T.children k).Nonempty
            · exact absurd he (hready k hk hch).ne_empty
            · exact ctg_leaf inst xs k (Finset.not_nonempty_iff_eq_empty.1 hch)
          exact wd (inst.W (T.stage k)) (rhs inst k (xs j)) (inst.c k) (C1.feas k) (C1.opt k)
            (hdual k hk).1.1 hPF
        · exact (ih _).2 q hq
      · rw [Function.update_of_ne hjj]; exact (ih j).2

end Valid

end NLS681

namespace NLS681

open StochasticProg StochasticProg.MultistageV2 Matrix

variable {H n m : ℕ} {T : Multistage.Tree H}

section Part2

lemma T1 (inst : Instance H n m T) (C : Cuts T n) (hterm : ∀ C', ¬ Step inst C C')
    {j : T.Node} {x : Fin n → ℝ} {θ : ℝ}
    (hp : IsProposal inst C j x θ) {k : T.Node} (hk : k ∈ T.children j) :
    ∃ x' θ', NLDSFeasible inst C k x x' θ' := by
  by_contra hinf
  obtain ⟨π, ρ, hd⟩ := l4 inst C k x hinf
  have hanc := (child_spec hk).2
  exact hterm _ (Step.feas C k (child_ne_root hk) x θ (by rw [hanc]; exact hp) hinf π ρ hd)

lemma T3 (inst : Instance H n m T) (C : Cuts T n) (xs : T.Node → Fin n → ℝ)
    (θs : T.Node → ℝ) (t : ℕ)
    (hall : ∀ j, (T.stage j).val ≤ t → NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) :
    ∀ j, (T.stage j).val ≤ t → IsProposal inst C j (xs j) (θs j) := by
  have key : ∀ s, ∀ j, (T.stage j).val = s → s ≤ t → IsProposal inst C j (xs j) (θs j) := by
    intro s
    induction s with
    | zero =>
      intro j hj ht
      have := T.root_unique j hj
      subst this
      exact IsProposal.root _ _ ((optl_root inst C _ 0 _ _).1 (hall _ (by omega)))
    | succ s ih =>
      intro j hj ht
      have hj0 : (T.stage j).val ≠ 0 := by omega
      have ha := T.anc_stage j hj0
      exact IsProposal.child j hj0 (xs (T.anc j)) (θs (T.anc j)) (xs j) (θs j)
        (ih (T.anc j) (by omega) (by omega)) (hall j (by omega))
  exact fun j hj => key _ j rfl hj

lemma T2 (inst : Instance H n m T)
    (hbdd : ∀ (t : Fin H) (b : Fin m → ℝ), ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (inst.W t).mulVec x = b → ∀ i, x i ≤ u i)
    (hrank : ∀ t : Fin H, LinearIndependent ℝ (fun r : Fin m => inst.W t r))
    (C : Cuts T n) (hterm : ∀ C', ¬ Step inst C C') (x : Fin n → ℝ) (θ : ℝ)
    (hx : NLDSOptimal inst C T.root 0 x θ) :
    ∃ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ), xs T.root = x ∧ θs T.root = θ ∧
      ∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j) := by
  classical
  have key : ∀ t : ℕ, ∃ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ), xs T.root = x ∧
      θs T.root = θ ∧ ∀ j, (T.stage j).val ≤ t → NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j) := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun _ => x, fun _ => θ, rfl, rfl, fun j hj => ?_⟩
      have := T.root_unique j (by omega)
      subst this
      exact (optl_root inst C _ _ _ _).1 hx
    | succ t ih =>
      obtain ⟨xs, θs, hr1, hr2, hall⟩ := ih
      have hprop := T3 inst C xs θs t hall
      have hex : ∀ j, (T.stage j).val = t + 1 → ∃ p : (Fin n → ℝ) × ℝ,
          NLDSOptimal inst C j (xs (T.anc j)) p.1 p.2 := by
        intro j hj
        have hj0 : (T.stage j).val ≠ 0 := by omega
        have ha := T.anc_stage j hj0
        obtain ⟨x', θ', hf⟩ := T1 inst C hterm (hprop (T.anc j) (by omega)) (anc_child hj0)
        obtain ⟨⟨x'', θ'', ho⟩, _⟩ := l5 inst hbdd hrank C j (xs (T.anc j)) ⟨x', θ', hf⟩
        exact ⟨(x'', θ''), ho⟩
      choose! f hf using hex
      refine ⟨fun j => if (T.stage j).val = t + 1 then (f j).1 else xs j,
        fun j => if (T.stage j).val = t + 1 then (f j).2 else θs j, ?_, ?_, fun j hj => ?_⟩
      · simp [T.root_stage, hr1]
      · simp [T.root_stage, hr2]
      · by_cases hjt : (T.stage j).val = t + 1
        · have hj0 : (T.stage j).val ≠ 0 := by omega
          have ha := T.anc_stage j hj0
          have hna : (T.stage (T.anc j)).val ≠ t + 1 := by omega
          simp only [if_pos hjt, if_neg hna]
          exact hf j hjt
        · simp only [if_neg hjt]
          by_cases hj0 : (T.stage j).val = 0
          · have := T.root_unique j hj0
            subst this
            exact (optl_root inst C _ _ _ _).1 (hall _ (by omega))
          · have ha := T.anc_stage j hj0
            have hna : (T.stage (T.anc j)).val ≠ t + 1 := by omega
            simp only [if_neg hna]
            exact hall j (by omega)
  obtain ⟨xs, θs, h1, h2, h3⟩ := key (H - 1)
  exact ⟨xs, θs, h1, h2, fun j => h3 j (by have := (T.stage j).isLt; omega)⟩

theorem part2 (inst : Instance H n m T)
    (hbdd : ∀ (t : Fin H) (b : Fin m → ℝ), ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (inst.W t).mulVec x = b → ∀ i, x i ≤ u i)
    (hrank : ∀ t : Fin H, LinearIndependent ℝ (fun r : Fin m => inst.W t r))
    (C : Cuts T n) (hC : Relation.ReflTransGen (Step inst) (Cuts.empty T n) C)
    (hterm : ∀ C' : Cuts T n, ¬ Step inst C C') :
      (((¬ ∃ x θ, NLDSFeasible inst C T.root 0 x θ) ∧ ¬ ∃ xs, Feasible inst xs) ∨
        ((∃ x θ, NLDSOptimal inst C T.root 0 x θ) ∧
          (∀ x θ, NLDSOptimal inst C T.root 0 x θ →
            ∃ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ), xs T.root = x ∧ θs T.root = θ ∧
              ∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) ∧
          ∀ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ),
            (∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) →
            Feasible inst xs ∧
            inst.c T.root ⬝ᵥ xs T.root + θs T.root = obj inst xs ∧
            ∀ xs', Feasible inst xs' → obj inst xs ≤ obj inst xs')) := by
  classical
  by_cases hroot : ∃ x θ, NLDSFeasible inst C T.root 0 x θ
  · right
    refine ⟨(l5 inst hbdd hrank C T.root 0 hroot).1,
      fun x θ hx => T2 inst hbdd hrank C hterm x θ hx, fun xs θs hopt => ?_⟩
    have hfeas : Feasible inst xs := fun k => ⟨(hopt k).1.1, (hopt k).1.2.1⟩
    have hprop : ∀ j, IsProposal inst C j (xs j) (θs j) := fun j =>
      T3 inst C xs θs (H - 1) (fun j _ => hopt j) j (by have := (T.stage j).isLt; omega)
    have hdu : ∀ j, ∃ (π : T.Node → Fin m → ℝ) (ρ : (k : T.Node) → C.feas k → ℝ)
        (σ : (k : T.Node) → C.opt k → ℝ),
        ∀ k ∈ T.children j, IsOptimalDualVertex inst C k (xs j) (π k) (ρ k) (σ k) := by
      intro j
      have hex : ∀ k, ∃ (πk : Fin m → ℝ) (ρk : C.feas k → ℝ) (σk : C.opt k → ℝ),
          k ∈ T.children j → IsOptimalDualVertex inst C k (xs j) πk ρk σk := by
        intro k
        by_cases hk : k ∈ T.children j
        · have hanc := (child_spec hk).2
          obtain ⟨_, π, ρ, σ, h⟩ := l5 inst hbdd hrank C k (xs j)
            ⟨xs k, θs k, by rw [← hanc]; exact (hopt k).1⟩
          exact ⟨π, ρ, σ, fun _ => h⟩
        · exact ⟨0, 0, 0, fun h => absurd h hk⟩
      choose π ρ σ hπ using hex
      exact ⟨π, ρ, σ, fun k hk => hπ k hk⟩
    -- T4: every node with children has optimality cuts
    have T4 : ∀ d : ℕ, ∀ j, H ≤ (T.stage j).val + d + 1 → (T.children j).Nonempty →
        (C.opt j).Nonempty := by
      intro d
      induction d with
      | zero =>
        intro j hj hch
        obtain ⟨k, hk⟩ := hch
        have h1 := (child_spec hk).1
        have h2 := (T.stage k).isLt
        omega
      | succ d ih =>
        intro j hj hch
        by_contra hne
        have hready : ∀ k ∈ T.children j, (T.children k).Nonempty → (C.opt k).Nonempty :=
          fun k hk hck => ih k (by have := (child_spec hk).1; omega) hck
        obtain ⟨π, ρ, σ, hπ⟩ := hdu j
        exact hterm _ (Step.opt C j hch (xs j) (θs j) (hprop j) hready π ρ σ hπ
          (Or.inl (Finset.not_nonempty_iff_eq_empty.1 hne)))
    have T4' : ∀ j, (T.children j).Nonempty → (C.opt j).Nonempty :=
      fun j => T4 H j (by omega)
    have hleaf : ∀ j, T.children j = ∅ → θs j = ctg inst xs j := by
      intro j hj
      rw [ctg_leaf inst xs j hj]
      exact (hopt j).1.2.2.2.2 (noch inst C hC j hj)
    have T5 : ∀ d : ℕ, ∀ j, H ≤ (T.stage j).val + d + 1 → θs j = ctg inst xs j := by
      intro d
      induction d with
      | zero =>
        intro j hj
        apply hleaf
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        have h1 := (child_spec hk).1
        have h2 := (T.stage k).isLt
        omega
      | succ d ih =>
        intro j hj
        by_cases hch : (T.children j).Nonempty
        · have hne := T4' j hch
          apply le_antisymm
          · have hc : NLDSFeasible inst C j (xs (T.anc j)) (xs j) (ctg inst xs j) :=
              ⟨(hopt j).1.1, (hopt j).1.2.1, (hopt j).1.2.2.1, (l6 inst C hC xs hfeas j).2,
                fun he => absurd he hne.ne_empty⟩
            have := (hopt j).2 _ _ hc
            linarith
          · obtain ⟨π, ρ, σ, hπ⟩ := hdu j
            have hready : ∀ k ∈ T.children j, (T.children k).Nonempty → (C.opt k).Nonempty :=
              fun k _ hck => T4' k hck
            have hn : ¬ (C.opt j = ∅ ∨ θs j < (optCut inst C j π ρ σ).2 -
                (optCut inst C j π ρ σ).1 ⬝ᵥ xs j) := fun hc =>
              hterm _ (Step.opt C j hch (xs j) (θs j) (hprop j) hready π ρ σ hπ hc)
            push Not at hn
            have h1 := hn.2
            rw [optCut_eval] at h1
            refine le_trans ?_ h1
            rw [ctg_eq]
            refine Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left ?_
              (div_nonneg (inst.hp_pos k).le (inst.hp_pos j).le))
            have hanc := (child_spec hk).2
            obtain ⟨x', θ', hf', heq⟩ := (hπ k hk).2
            have h2 := (hopt k).2 x' θ' (by rw [hanc]; exact hf')
            have h3 := ih k (by have := (child_spec hk).1; omega)
            rw [← h3]
            linarith
        · exact hleaf j (Finset.not_nonempty_iff_eq_empty.1 hch)
    have T5' : ∀ j, θs j = ctg inst xs j := fun j => T5 H j (by omega)
    refine ⟨hfeas, by rw [T5', obj_eq], fun xs' hxs' => ?_⟩
    have hc : NLDSFeasible inst C T.root (xs (T.anc T.root)) (xs' T.root) (ctg inst xs' T.root) := by
      refine ⟨(hxs' T.root).1, ?_, (l6 inst C hC xs' hxs' T.root).1,
        (l6 inst C hC xs' hxs' T.root).2, fun he => ?_⟩
      · have := (hxs' T.root).2
        rw [rhs_root] at this ⊢
        exact this
      · by_cases hch : (T.children T.root).Nonempty
        · exact absurd he (T4' _ hch).ne_empty
        · exact ctg_leaf inst xs' _ (Finset.not_nonempty_iff_eq_empty.1 hch)
    have h1 := (hopt T.root).2 _ _ hc
    rw [T5', ← obj_eq, ← obj_eq] at h1
    exact h1
  · left
    refine ⟨hroot, fun ⟨xs, hxs⟩ => hroot ⟨xs T.root,
      if C.opt T.root = ∅ then 0 else ctg inst xs T.root, (hxs T.root).1, ?_,
      (l6 inst C hC xs hxs T.root).1, fun q hq => ?_, fun he => by rw [if_pos he]⟩⟩
    · have := (hxs T.root).2
      rw [rhs_root] at this ⊢
      exact this
    · rw [if_neg (Finset.ne_empty_of_mem hq)]
      exact (l6 inst C hC xs hxs T.root).2 q hq

end Part2

end NLS681

open StochasticProg StochasticProg.MultistageV2 in
theorem solution {H n m : ℕ} {T : Multistage.Tree H} (inst : Instance H n m T)
    -- all `x_t` have finite upper bounds (pp. 267–268), bounds being rows of (1.2)
    (hbdd : ∀ (t : Fin H) (b : Fin m → ℝ), ∃ u : Fin n → ℝ, ∀ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i) → (inst.W t).mulVec x = b → ∀ i, x i ≤ u i)
    -- standard form with full row rank: basic (dual) solutions exist (p. 267)
    (hrank : ∀ t : Fin H, LinearIndependent ℝ (fun r : Fin m => inst.W t r)) :
    (¬ ∃ s : ℕ → Cuts T n, s 0 = Cuts.empty T n ∧ ∀ i, Step inst (s i) (s (i + 1))) ∧
    ∀ C : Cuts T n, Relation.ReflTransGen (Step inst) (Cuts.empty T n) C →
      (∀ C' : Cuts T n, ¬ Step inst C C') →
      (((¬ ∃ x θ, NLDSFeasible inst C T.root 0 x θ) ∧ ¬ ∃ xs, Feasible inst xs) ∨
        ((∃ x θ, NLDSOptimal inst C T.root 0 x θ) ∧
          (∀ x θ, NLDSOptimal inst C T.root 0 x θ →
            ∃ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ), xs T.root = x ∧ θs T.root = θ ∧
              ∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) ∧
          ∀ (xs : T.Node → Fin n → ℝ) (θs : T.Node → ℝ),
            (∀ j, NLDSOptimal inst C j (xs (T.anc j)) (xs j) (θs j)) →
            Feasible inst xs ∧
            inst.c T.root ⬝ᵥ xs T.root + θs T.root = obj inst xs ∧
            ∀ xs', Feasible inst xs' → obj inst xs ≤ obj inst xs')) := by
  exact ⟨NLS681.part1 inst, fun C hC hterm => NLS681.part2 inst hbdd hrank C hC hterm⟩
