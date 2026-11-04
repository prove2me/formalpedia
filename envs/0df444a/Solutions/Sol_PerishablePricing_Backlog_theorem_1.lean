-- Prove2me | solution 1 for PerishablePricing.Backlog.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:45:32.254186+00:00
-- url     : https://prove2.me/submissions/9fbaa475-183d-444a-bcd4-744d07acbc0d

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PPBSol
open PerishablePricing.Backlog MeasureTheory

lemma lnatConcave_iff {ι : Type*} (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) :
    LNatConcaveOn S f ↔ LNatConvexSet S ∧ ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℝ, 0 ≤ α →
      f u + f v ≤ f ((u + α • (1 : ι → ℝ)) ⊓ v) + f (u ⊔ (v - α • (1 : ι → ℝ))) := by
  unfold LNatConcaveOn LNatConvexOn
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu v hv α hα => ?_⟩
    have := h2 u hu v hv α hα
    simp only [Pi.neg_apply] at this
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu v hv α hα => ?_⟩
    have := h2 u hu v hv α hα
    simp only [Pi.neg_apply]
    linarith

lemma pinf {ι : Type*} (u v : ι → ℝ) (α : ℝ) (i : ι) :
    ((u + α • (1 : ι → ℝ)) ⊓ v) i = min (u i + α) (v i) := by
  simp [Pi.inf_apply]

lemma psup {ι : Type*} (u v : ι → ℝ) (α : ℝ) (i : ι) :
    (u ⊔ (v - α • (1 : ι → ℝ))) i = max (u i) (v i - α) := by
  simp [Pi.sup_apply]

lemma lnatSet_inter {ι : Type*} {S T : Set (ι → ℝ)} (hS : LNatConvexSet S)
    (hT : LNatConvexSet T) : LNatConvexSet (S ∩ T) := by
  rintro u ⟨huS, huT⟩ v ⟨hvS, hvT⟩ α hα
  exact ⟨⟨(hS u huS v hvS α hα).1, (hT u huT v hvT α hα).1⟩,
    ⟨(hS u huS v hvS α hα).2, (hT u huT v hvT α hα).2⟩⟩

lemma lnatSet_le {ι : Type*} (i j : ι) (c : ℝ) : LNatConvexSet {w : ι → ℝ | w i + c ≤ w j} := by
  intro u hu v hv α hα
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  rw [pinf, pinf, psup, psup]
  constructor
  · rcases le_total (u j + α) (v j) with h | h
    · rw [min_eq_left h]
      have : min (u i + α) (v i) ≤ u i + α := min_le_left _ _
      linarith
    · rw [min_eq_right h]
      have : min (u i + α) (v i) ≤ v i := min_le_right _ _
      linarith
  · rcases le_total (u i) (v i - α) with h | h
    · rw [max_eq_right h]
      have : v j - α ≤ max (u j) (v j - α) := le_max_right _ _
      linarith
    · rw [max_eq_left h]
      have : u j ≤ max (u j) (v j - α) := le_max_left _ _
      linarith

lemma lnatSet_ge {ι : Type*} (i : ι) (c : ℝ) : LNatConvexSet {w : ι → ℝ | c ≤ w i} := by
  intro u hu v hv α hα
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  rw [pinf, psup]
  exact ⟨le_min (by linarith) hv, le_trans hu (le_max_left _ _)⟩

lemma lnatSet_le' {ι : Type*} (i : ι) (c : ℝ) : LNatConvexSet {w : ι → ℝ | w i ≤ c} := by
  intro u hu v hv α hα
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  rw [pinf, psup]
  exact ⟨le_trans (min_le_right _ _) hv, max_le hu (by linarith)⟩

lemma V_lnat (n m : ℕ) : LNatConvexSet (V n m) := by
  intro u hu v hv α hα
  simp only [V, Set.mem_setOf_eq] at hu hv ⊢
  constructor
  · intro i j hij hj
    rw [pinf, pinf]
    exact min_le_min (by linarith [hu i j hij hj]) (hv i j hij hj)
  · intro i j hij hj
    rw [psup, psup]
    exact max_le_max (hu i j hij hj) (by linarith [hv i j hij hj])

lemma lin_eq {ι : Type*} (u v : ι → ℝ) (α : ℝ) (i : ι) :
    ((u + α • (1 : ι → ℝ)) ⊓ v) i + (u ⊔ (v - α • (1 : ι → ℝ))) i = u i + v i := by
  rw [pinf, psup]
  rcases le_total (u i + α) (v i) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

lemma pos_aux (X Y pd qd : ℝ) (h1 : X ≤ pd) (h2 : pd ≤ Y) (h3 : pd + qd = X + Y) :
    max pd 0 + max qd 0 ≤ max X 0 + max Y 0 := by
  rcases le_total pd 0 with a | a <;> rcases le_total qd 0 with b | b <;>
    rcases le_total X 0 with c | c <;> rcases le_total Y 0 with d | d <;>
    simp only [max_eq_left, max_eq_right, a, b, c, d] <;> linarith

lemma diff_ineq {ι : Type*} (u v : ι → ℝ) (α : ℝ) (i j : ι) :
    max (((u + α • (1 : ι → ℝ)) ⊓ v) i - ((u + α • (1 : ι → ℝ)) ⊓ v) j) 0 +
      max ((u ⊔ (v - α • (1 : ι → ℝ))) i - (u ⊔ (v - α • (1 : ι → ℝ))) j) 0 ≤
      max (u i - u j) 0 + max (v i - v j) 0 := by
  rw [pinf, pinf, psup, psup]
  rcases le_total (u i + α) (v i) with hi | hi <;>
    rcases le_total (u j + α) (v j) with hj | hj
  · rw [min_eq_left hi, min_eq_left hj, max_eq_right (by linarith : u i ≤ v i - α),
      max_eq_right (by linarith : u j ≤ v j - α)]
    apply le_of_eq; congr 1 <;> congr 1 <;> ring
  · rw [min_eq_left hi, min_eq_right hj, max_eq_right (by linarith : u i ≤ v i - α),
      max_eq_left (by linarith : v j - α ≤ u j)]
    exact pos_aux _ _ _ _ (by linarith) (by linarith) (by ring)
  · rw [min_eq_right hi, min_eq_left hj, max_eq_left (by linarith : v i - α ≤ u i),
      max_eq_right (by linarith : u j ≤ v j - α)]
    have := pos_aux (v i - v j) (u i - u j) (v i - (u j + α)) (u i - (v j - α))
      (by linarith) (by linarith) (by ring)
    linarith
  · rw [min_eq_right hi, min_eq_right hj, max_eq_left (by linarith : v i - α ≤ u i),
      max_eq_left (by linarith : v j - α ≤ u j)]
    linarith

/-- Lemma 1 type: composition with `w ↦ (w (σ i) - w j0)_i`. -/
lemma comp_ineq {ι J : Type*} (S : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ)
    (hF : ∀ u ∈ S, ∀ v ∈ S, ∀ α : ℝ, 0 ≤ α →
      F u + F v ≤ F ((u + α • (1 : ι → ℝ)) ⊓ v) + F (u ⊔ (v - α • (1 : ι → ℝ))))
    (σ : ι → J) (j0 : J) (u v : J → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hu : (fun i => u (σ i) - u j0) ∈ S) (hv : (fun i => v (σ i) - v j0) ∈ S) :
    F (fun i => u (σ i) - u j0) + F (fun i => v (σ i) - v j0) ≤
      F (fun i => ((u + α • (1 : J → ℝ)) ⊓ v) (σ i) - ((u + α • (1 : J → ℝ)) ⊓ v) j0) +
      F (fun i => (u ⊔ (v - α • (1 : J → ℝ))) (σ i) - (u ⊔ (v - α • (1 : J → ℝ))) j0) := by
  set Tu : ι → ℝ := fun i => u (σ i) - u j0
  set Tv : ι → ℝ := fun i => v (σ i) - v j0
  rcases le_total (u j0 + α) (v j0) with h | h
  · set β := v j0 - u j0 - α
    have hβ : 0 ≤ β := by simp only [β]; linarith
    have e1 : (fun i => ((u + α • (1 : J → ℝ)) ⊓ v) (σ i) - ((u + α • (1 : J → ℝ)) ⊓ v) j0)
        = (Tv + β • (1 : ι → ℝ)) ⊓ Tu := by
      funext i
      rw [pinf, pinf, pinf, min_eq_left h]
      simp only [Tu, Tv, β]
      rw [min_comm]
      rw [← min_sub_sub_right]
      congr 1 <;> ring
    have e2 : (fun i => (u ⊔ (v - α • (1 : J → ℝ))) (σ i) - (u ⊔ (v - α • (1 : J → ℝ))) j0)
        = Tv ⊔ (Tu - β • (1 : ι → ℝ)) := by
      funext i
      rw [psup, psup, psup, max_eq_right (by linarith : u j0 ≤ v j0 - α)]
      simp only [Tu, Tv, β]
      rw [max_comm, ← max_sub_sub_right]
      congr 1 <;> ring
    rw [e1, e2]
    have := hF Tv hv Tu hu β hβ
    linarith
  · set β := u j0 + α - v j0
    have hβ : 0 ≤ β := by simp only [β]; linarith
    have e1 : (fun i => ((u + α • (1 : J → ℝ)) ⊓ v) (σ i) - ((u + α • (1 : J → ℝ)) ⊓ v) j0)
        = (Tu + β • (1 : ι → ℝ)) ⊓ Tv := by
      funext i
      rw [pinf, pinf, pinf, min_eq_right h]
      simp only [Tu, Tv, β]
      rw [← min_sub_sub_right]
      congr 1 <;> ring
    have e2 : (fun i => (u ⊔ (v - α • (1 : J → ℝ))) (σ i) - (u ⊔ (v - α • (1 : J → ℝ))) j0)
        = Tu ⊔ (Tv - β • (1 : ι → ℝ)) := by
      funext i
      rw [psup, psup, psup, max_eq_left (by linarith : v j0 - α ≤ u j0)]
      simp only [Tu, Tv, β]
      rw [← max_sub_sub_right]
      congr 1 <;> ring
    rw [e1, e2]
    exact hF Tu hu Tv hv β hβ

lemma sum_sSup_le {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty) (C : ℝ)
    (h : ∀ s ∈ S, ∀ t ∈ T, s + t ≤ C) : sSup S + sSup T ≤ C := by
  have h1 : ∀ s ∈ S, s ≤ C - sSup T := by
    intro s hs
    have : sSup T ≤ C - s := csSup_le hT (fun t ht => by linarith [h s hs t ht])
    linarith
  have := csSup_le hS h1
  linarith

/-- Lemma 2 type (partial supremum). -/
lemma partial_sup {ι J Y : Type*} (D : Set (J → ℝ)) (F : (J → ℝ) → ℝ)
    (join : (ι → ℝ) → Y → (J → ℝ))
    (hD : LNatConvexSet D)
    (hF : ∀ u ∈ D, ∀ v ∈ D, ∀ α : ℝ, 0 ≤ α →
      F u + F v ≤ F ((u + α • (1 : J → ℝ)) ⊓ v) + F (u ⊔ (v - α • (1 : J → ℝ))))
    (hj : ∀ (x x' : ι → ℝ) (y y' : Y) (α : ℝ), ∃ y1 y2 : Y,
      (join x y + α • (1 : J → ℝ)) ⊓ join x' y' = join ((x + α • (1 : ι → ℝ)) ⊓ x') y1 ∧
      join x y ⊔ (join x' y' - α • (1 : J → ℝ)) = join (x ⊔ (x' - α • (1 : ι → ℝ))) y2)
    (hbdd : ∀ x, (∃ y, join x y ∈ D) →
      BddAbove ((fun y => F (join x y)) '' {y | join x y ∈ D})) :
    LNatConcaveOn {x | ∃ y, join x y ∈ D}
      (fun x => sSup ((fun y => F (join x y)) '' {y | join x y ∈ D})) := by
  rw [lnatConcave_iff]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy⟩ x' ⟨y', hy'⟩ α hα
    obtain ⟨y1, y2, e1, e2⟩ := hj x x' y y' α
    have := hD _ hy _ hy' α hα
    rw [e1, e2] at this
    exact ⟨⟨y1, this.1⟩, ⟨y2, this.2⟩⟩
  · rintro x ⟨y0, hy0⟩ x' ⟨y0', hy0'⟩ α hα
    apply sum_sSup_le (Set.Nonempty.image _ ⟨y0, hy0⟩) (Set.Nonempty.image _ ⟨y0', hy0'⟩)
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    obtain ⟨y1, y2, e1, e2⟩ := hj x x' y y' α
    have hm := hD _ hy _ hy' α hα
    have := hF _ hy _ hy' α hα
    rw [e1, e2] at this hm
    have b1 := le_csSup (hbdd _ ⟨y1, hm.1⟩) ⟨y1, hm.1, rfl⟩
    have b2 := le_csSup (hbdd _ ⟨y2, hm.2⟩) ⟨y2, hm.2, rfl⟩
    simp only at b1 b2 ⊢
    linarith

/-- concave function of one variable: L♮ inequality. -/
lemma concave_pair (R : ℝ → ℝ) (lo hi : ℝ) (hR : ConcaveOn ℝ (Set.Icc lo hi) R)
    (x y α : ℝ) (hα : 0 ≤ α) (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) :
    R x + R y ≤ R (min (x + α) y) + R (max x (y - α)) := by
  rcases le_total (x + α) y with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    rcases eq_or_lt_of_le hα with h0 | h0
    · subst h0; simp
    have hxy : x < y := by linarith
    -- x + α = t x + (1-t) y with t = (y - x - α)/(y - x)
    set t := (y - x - α) / (y - x)
    have hyx : 0 < y - x := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hyx.le
    have ht1 : 0 ≤ 1 - t := by
      have : t ≤ 1 := by rw [div_le_one hyx]; linarith
      linarith
    have e1 : t • x + (1 - t) • y = x + α := by
      simp only [smul_eq_mul, t]; field_simp; ring
    have e2 : (1 - t) • x + t • y = y - α := by
      simp only [smul_eq_mul, t]; field_simp; ring
    have c1 := hR.2 hx hy ht0 ht1 (by ring)
    have c2 := hR.2 hx hy ht1 ht0 (by ring)
    rw [e1] at c1
    rw [e2] at c2
    simp only [smul_eq_mul] at c1 c2
    nlinarith
  · rw [min_eq_right h, max_eq_left (by linarith)]
    linarith

end PPBSol


namespace PerishablePricing.Backlog.Model
open PPBSol MeasureTheory

variable {L k : ℕ} (M : Model L k)

lemma ext_castSucc (s : Fin L → ℝ) (sl : ℝ) (i : Fin L) : Model.ext s sl i.castSucc = s i := by
  simp [Model.ext]

lemma ext_last (s : Fin L → ℝ) (sl : ℝ) : Model.ext s sl (Fin.last L) = sl := by
  simp [Model.ext]

lemma ext_shift (s : Fin L → ℝ) (sl δ : ℝ) :
    Model.ext (s + δ • (1 : Fin L → ℝ)) (sl + δ) = Model.ext s sl + δ • (1 : Fin (L+1) → ℝ) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Model.ext]
  | cast j => simp [Model.ext]

lemma ext_mono {s s' : Fin L → ℝ} {sl sl' : ℝ} (hs : s ≤ s') (hsl : sl ≤ sl') :
    Model.ext s sl ≤ Model.ext s' sl' := by
  intro i
  induction i using Fin.lastCases with
  | last => simp [Model.ext, hsl]
  | cast j => rw [ext_castSucc, ext_castSucc]; exact hs j

lemma sLast_def (s : Fin L → ℝ) : M.sLast s = s ⟨L - 1, by have := M.one_le_L; omega⟩ := rfl

lemma s1_def (s : Fin L → ℝ) : M.s1 s = s ⟨0, by have := M.one_le_L; omega⟩ := rfl

lemma ext_ordered {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ} (hsl : M.sLast s ≤ sl) :
    ∀ i j : Fin (L+1), i ≤ j → Model.ext s sl i ≤ Model.ext s sl j := by
  have hL := M.one_le_L
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact le_rfl
    | cast i' =>
      rw [ext_castSucc, ext_last]
      refine le_trans (hs i' ⟨L - 1, by omega⟩ ?_ ?_) hsl
      · rw [Fin.le_def]; simp; omega
      · simp; omega
  | cast j' =>
    induction i using Fin.lastCases with
    | last =>
      exfalso
      rw [Fin.le_def] at hij
      simp at hij
      omega
    | cast i' =>
      rw [ext_castSucc, ext_castSucc]
      exact hs i' j' (by simpa using hij) j'.2

lemma s1_shift (s : Fin L → ℝ) (δ : ℝ) : M.s1 (s + δ • (1 : Fin L → ℝ)) = M.s1 s + δ := by
  simp [Model.s1]

lemma sLast_shift (s : Fin L → ℝ) (δ : ℝ) :
    M.sLast (s + δ • (1 : Fin L → ℝ)) = M.sLast s + δ := by
  simp [Model.sLast]

lemma netInv_shift (s : Fin L → ℝ) (sl δ : ℝ) :
    M.netInv (s + δ • (1 : Fin L → ℝ)) (sl + δ) = M.netInv s sl + δ := by
  unfold Model.netInv
  rw [ext_shift]
  simp

lemma netInv_mono {s s' : Fin L → ℝ} {sl sl' : ℝ} (hs : s ≤ s') (hsl : sl ≤ sl') :
    M.netInv s sl ≤ M.netInv s' sl' := by
  unfold Model.netInv
  exact ext_mono hs hsl _

lemma s1_le_netInv {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ} (hsl : M.sLast s ≤ sl) :
    M.s1 s ≤ M.netInv s sl := by
  have hL := M.one_le_L
  have h := M.ext_ordered hs hsl ⟨0, by omega⟩ ⟨L - k, by have := M.k_le_L; omega⟩
    (by rw [Fin.le_def]; simp)
  have e : Model.ext s sl ⟨0, by omega⟩ = M.s1 s := by
    have : (⟨0, by omega⟩ : Fin (L+1)) = Fin.castSucc ⟨0, by omega⟩ := rfl
    rw [this, ext_castSucc]; rfl
  rw [e] at h
  exact h

lemma s1_le_sLast {s : Fin L → ℝ} (hs : s ∈ V L L) : M.s1 s ≤ M.sLast s := by
  have hL := M.one_le_L
  exact hs _ _ (by rw [Fin.le_def]; simp) (by simp; omega)

lemma V_shift {n m : ℕ} {s : Fin n → ℝ} (hs : s ∈ V n m) (δ : ℝ) :
    s + δ • (1 : Fin n → ℝ) ∈ V n m := by
  intro i j hij hj
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  linarith [hs i j hij hj]

lemma next_mem {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ} (hsl : M.sLast s ≤ sl) (a : ℝ) :
    Model.next s sl a ∈ V L L := by
  intro i j hij hj
  unfold Model.next
  have := M.ext_ordered hs hsl i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)
  linarith

lemma next_sub (s : Fin L → ℝ) (sl a a' : ℝ) :
    Model.next s sl a' = Model.next s sl a - (a' - a) • (1 : Fin L → ℝ) := by
  funext i
  simp [Model.next]

lemma next_shift (s : Fin L → ℝ) (sl δ a : ℝ) :
    Model.next (s + δ • (1 : Fin L → ℝ)) (sl + δ) a = Model.next s sl a + δ • (1 : Fin L → ℝ) := by
  funext i
  have := congrFun (ext_shift s sl δ) i.succ
  simp only [Model.next, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at this ⊢
  rw [this]
  ring

lemma sLast_next (s : Fin L → ℝ) (sl a : ℝ) : M.sLast (Model.next s sl a) = sl - a := by
  have hL := M.one_le_L
  unfold Model.sLast Model.next
  have : (⟨L - 1, by omega⟩ : Fin L).succ = Fin.last L := by
    ext; simp; omega
  rw [this, ext_last]

lemma phi_eq (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d a ε : ℝ) :
    M.phi F s sl d a ε = M.γ * M.c * (sl - a) - M.c * sl - M.θ * (a - (d + ε))
      - M.hp * max (M.netInv s sl - a) 0 - M.hm * max (a - M.netInv s sl) 0
      + M.γ * F (Model.next s sl a) := by
  unfold Model.phi
  rw [sLast_next]

lemma phi_eps (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d a ε ε' : ℝ) :
    M.phi F s sl d a ε' = M.phi F s sl d a ε + M.θ * (ε' - ε) := by
  unfold Model.phi; ring

/-- Lipschitz-type property in the direction `-e`. -/
def LBp (F : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ x ∈ V L L, ∀ δ : ℝ, 0 ≤ δ → F (x - δ • (1 : Fin L → ℝ)) ≤ F x + (M.θ + M.c) * δ

/-- Upper bound property. -/
def UBp (F : (Fin L → ℝ) → ℝ) : Prop :=
  ∃ K β : ℝ, 0 ≤ β ∧ β ≤ M.c ∧ ∀ y ∈ V L L, F y ≤ K - β * M.sLast y

section P
variable {M}
variable {F : (Fin L → ℝ) → ℝ} {s : Fin L → ℝ} {sl : ℝ}

lemma lo_le_hi (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε : ℝ) :
    max (M.s1 s) (d + ε) ≤ max (M.netInv s sl) (d + ε) :=
  max_le_max (M.s1_le_netInv hs hsl) le_rfl

lemma phi_le_lo (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε a : ℝ)
    (ha : max (M.s1 s) (d + ε) ≤ a) :
    M.phi F s sl d a ε ≤ M.phi F s sl d (max (M.s1 s) (d + ε)) ε +
      M.hp * (max (M.netInv s sl) (d + ε) - max (M.s1 s) (d + ε)) := by
  set lo := max (M.s1 s) (d + ε)
  set hi := max (M.netInv s sl) (d + ε)
  set N := M.netInv s sl
  have hlh : lo ≤ hi := lo_le_hi hs hsl d ε
  have hn := hLB (Model.next s sl lo) (M.next_mem hs hsl lo) (a - lo) (by linarith)
  rw [← next_sub s sl lo a] at hn
  rw [phi_eq, phi_eq]
  have hγ := M.γ_nonneg
  have hγ1 := M.γ_le_one
  have h1 : M.γ * F (Model.next s sl a) ≤ M.γ * (F (Model.next s sl lo) + (M.θ + M.c) * (a - lo)) :=
    mul_le_mul_of_nonneg_left hn hγ
  have hNhi : N ≤ hi := le_max_left _ _
  have h2 : max (N - lo) 0 - max (N - a) 0 ≤ hi - lo := by
    have : max (N - lo) 0 ≤ hi - lo := max_le (by linarith) (by linarith)
    have : 0 ≤ max (N - a) 0 := le_max_right _ _
    linarith
  have h2' : M.hp * (max (N - lo) 0 - max (N - a) 0) ≤ M.hp * (hi - lo) :=
    mul_le_mul_of_nonneg_left h2 M.hp_nonneg
  have h3 : M.hm * max (lo - N) 0 ≤ M.hm * max (a - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) M.hm_nonneg
  have h4 : 0 ≤ (1 - M.γ) * M.θ * (a - lo) :=
    mul_nonneg (mul_nonneg (by linarith) M.θ_nonneg) (by linarith)
  linarith

lemma phi_bdd (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε : ℝ) :
    BddAbove ((fun a => M.phi F s sl d a ε) '' Set.Ici (max (M.s1 s) (d + ε))) := by
  refine ⟨M.phi F s sl d (max (M.s1 s) (d + ε)) ε +
      M.hp * (max (M.netInv s sl) (d + ε) - max (M.s1 s) (d + ε)), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact phi_le_lo hLB hs hsl d ε a ha

lemma phi_diff (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε a a' : ℝ)
    (ha : max (M.netInv s sl) (d + ε) ≤ a) :
    M.phi F s sl d a' ε - M.phi F s sl d a ε =
      -(M.γ * M.c + M.θ + M.hm) * (a' - a) +
        M.γ * (F (Model.next s sl a') - F (Model.next s sl a)) ∨ a' < a := by
  rcases lt_or_ge a' a with h | h
  · exact Or.inr h
  left
  have hN : M.netInv s sl ≤ a := le_trans (le_max_left _ _) ha
  rw [phi_eq, phi_eq, max_eq_right (by linarith : M.netInv s sl - a ≤ 0),
    max_eq_right (by linarith : M.netInv s sl - a' ≤ 0),
    max_eq_left (by linarith : 0 ≤ a - M.netInv s sl),
    max_eq_left (by linarith : 0 ≤ a' - M.netInv s sl)]
  ring

lemma phi_beyond (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε a a' : ℝ)
    (ha : max (M.netInv s sl) (d + ε) ≤ a) (haa : a ≤ a') :
    M.phi F s sl d a' ε ≤ M.phi F s sl d a ε := by
  rcases phi_diff (F := F) hs hsl d ε a a' ha with h | h
  · have hn := hLB (Model.next s sl a) (M.next_mem hs hsl a) (a' - a) (by linarith)
    rw [← next_sub s sl a a'] at hn
    have h1 : M.γ * (F (Model.next s sl a') - F (Model.next s sl a)) ≤ M.γ * ((M.θ + M.c) * (a' - a)) :=
      mul_le_mul_of_nonneg_left (by linarith) M.γ_nonneg
    have h4 : 0 ≤ (1 - M.γ) * M.θ * (a' - a) :=
      mul_nonneg (mul_nonneg (by linarith [M.γ_le_one]) M.θ_nonneg) (by linarith)
    have h5 : 0 ≤ M.hm * (a' - a) := mul_nonneg M.hm_nonneg (by linarith)
    linarith
  · linarith

lemma g_eq_gtilde (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d ε : ℝ) :
    M.g F s sl d ε = M.gtilde F s sl d ε := by
  unfold Model.g Model.gtilde Model.depletionSet
  set lo := max (M.s1 s) (d + ε)
  set hi := max (M.netInv s sl) (d + ε)
  have hlh : lo ≤ hi := lo_le_hi hs hsl d ε
  have hsub : Set.Icc lo hi ⊆ Set.Ici lo := fun x hx => hx.1
  have hB := phi_bdd hLB hs hsl d ε
  have hne : ((fun a => M.phi F s sl d a ε) '' Set.Icc lo hi).Nonempty :=
    ⟨_, lo, ⟨le_rfl, hlh⟩, rfl⟩
  apply le_antisymm
  · exact csSup_le_csSup hB hne (Set.image_mono hsub)
  · apply csSup_le (hne.mono (Set.image_mono hsub))
    rintro _ ⟨a, ha, rfl⟩
    have hB' := hB.mono (Set.image_mono hsub)
    by_cases h : a ≤ hi
    · exact le_csSup hB' ⟨a, ⟨ha, h⟩, rfl⟩
    · exact le_trans (phi_beyond hLB hs hsl d ε hi a le_rfl (by linarith))
        (le_csSup hB' ⟨hi, ⟨hlh, le_rfl⟩, rfl⟩)

lemma gtilde_anti (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d : ℝ) :
    Antitone (fun ε => M.gtilde F s sl d ε - M.θ * ε) := by
  intro e1 e2 h12
  simp only
  unfold Model.gtilde
  have hne : ((fun a => M.phi F s sl d a e2) '' Set.Ici (max (M.s1 s) (d + e2))).Nonempty :=
    ⟨_, ⟨_, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  have : sSup ((fun a => M.phi F s sl d a e2) '' Set.Ici (max (M.s1 s) (d + e2))) ≤
      sSup ((fun a => M.phi F s sl d a e1) '' Set.Ici (max (M.s1 s) (d + e1))) +
        M.θ * (e2 - e1) := by
    apply csSup_le hne
    rintro _ ⟨a, ha, rfl⟩
    have ha' : max (M.s1 s) (d + e1) ≤ a :=
      le_trans (max_le_max le_rfl (by linarith)) ha
    simp only
    rw [M.phi_eps F s sl d a e1 e2]
    have := le_csSup (phi_bdd hLB hs hsl d e1) ⟨a, ha', rfl⟩
    simp only at this
    linarith
  linarith

lemma ae_supp : ∀ᵐ ε ∂M.μ, ε ∈ Set.Icc M.A M.B := by
  rw [ae_iff]
  exact M.support

lemma g_integrable (hLB : M.LBp F) (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) (d : ℝ) :
    Integrable (fun ε => M.g F s sl d ε) M.μ := by
  have : IsProbabilityMeasure M.μ := M.isProb
  set h := fun ε => M.gtilde F s sl d ε - M.θ * ε
  have hanti : Antitone h := gtilde_anti hLB hs hsl d
  have heq : (fun ε => M.g F s sl d ε) = fun ε => h ε + M.θ * ε := by
    funext ε
    simp only [h]
    rw [g_eq_gtilde hLB hs hsl d ε]
    ring
  rw [heq]
  have hmeas : Measurable (fun ε => h ε + M.θ * ε) :=
    hanti.measurable.add (measurable_id.const_mul _)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (|h M.A| + |h M.B| + M.θ * (|M.A| + |M.B|)) ?_
  filter_upwards [ae_supp (M := M)] with ε hε
  have h1 : h M.B ≤ h ε := hanti hε.2
  have h2 : h ε ≤ h M.A := hanti hε.1
  have hθ := M.θ_nonneg
  rw [Real.norm_eq_abs, abs_le]
  have a1 := abs_nonneg (h M.A); have a2 := abs_nonneg (h M.B)
  have a3 := le_abs_self (h M.A); have a4 := neg_abs_le (h M.B)
  have a5 : M.θ * ε ≤ M.θ * (|M.A| + |M.B|) := by
    apply mul_le_mul_of_nonneg_left _ hθ
    have := le_abs_self M.B; have := abs_nonneg M.A; linarith [hε.2]
  have a6 : -(M.θ * (|M.A| + |M.B|)) ≤ M.θ * ε := by
    rw [← mul_neg]
    apply mul_le_mul_of_nonneg_left _ hθ
    have := neg_abs_le M.A; have := abs_nonneg M.B; linarith [hε.1]
  constructor <;> linarith

lemma g_le {K β : ℝ} (hβc : β ≤ M.c) (hF : ∀ y ∈ V L L, F y ≤ K - β * M.sLast y)
    (hs : s ∈ V L L) (hsl : M.sLast s ≤ sl) {d ε : ℝ} (hd : d ∈ Set.Icc M.dlo M.dhi)
    (hε : ε ∈ Set.Icc M.A M.B) :
    M.g F s sl d ε ≤ M.γ * K - ((1 - M.γ) * M.c + M.γ * β) * sl := by
  unfold Model.g Model.depletionSet
  apply csSup_le ((Set.nonempty_Icc.mpr (lo_le_hi hs hsl d ε)).image _)
  rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
  simp only
  rw [phi_eq]
  have hy := hF (Model.next s sl a) (M.next_mem hs hsl a)
  rw [sLast_next] at hy
  have hdt : 0 ≤ d + ε := by linarith [hd.1, hε.1, M.demand_nonneg]
  have ha : d + ε ≤ a := le_trans (le_max_right _ _) ha1
  have hγ := M.γ_nonneg
  have e1 : M.γ * F (Model.next s sl a) ≤ M.γ * (K - β * (sl - a)) := mul_le_mul_of_nonneg_left hy hγ
  have e2 : 0 ≤ M.θ * (a - (d + ε)) := mul_nonneg M.θ_nonneg (by linarith)
  have e3 : 0 ≤ M.hp * max (M.netInv s sl - a) 0 := mul_nonneg M.hp_nonneg (le_max_right _ _)
  have e4 : 0 ≤ M.hm * max (a - M.netInv s sl) 0 := mul_nonneg M.hm_nonneg (le_max_right _ _)
  have e5 : 0 ≤ M.γ * (M.c - β) * a := mul_nonneg (mul_nonneg hγ (by linarith)) (by linarith)
  linarith

end P

lemma revenue_bdd : ∃ R : ℝ, ∀ d ∈ Set.Icc M.dlo M.dhi, M.P d * d ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_Icc).bddAbove_image M.revenue_continuous
  exact ⟨R, fun d hd => hR ⟨d, hd, rfl⟩⟩

/-- The Bellman operator. -/
noncomputable def T (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => M.G F s p.1 p.2) '' M.orderSet s)

lemma f_succ (n : ℕ) : M.f (n + 1) = M.T (M.f n) := rfl

lemma orderSet_ne (s : Fin L → ℝ) : (M.orderSet s).Nonempty :=
  ⟨(M.sLast s, M.dlo), le_rfl, le_rfl, M.dlo_le_dhi⟩

section Q
variable {M}
variable {F : (Fin L → ℝ) → ℝ}

lemma G_le (hLB : M.LBp F) {K β R : ℝ} (hβc : β ≤ M.c)
    (hF : ∀ y ∈ V L L, F y ≤ K - β * M.sLast y)
    (hR : ∀ d ∈ Set.Icc M.dlo M.dhi, M.P d * d ≤ R)
    {s : Fin L → ℝ} (hs : s ∈ V L L) {sl d : ℝ} (hsl : M.sLast s ≤ sl)
    (hd : d ∈ Set.Icc M.dlo M.dhi) :
    M.G F s sl d ≤ R + M.γ * K - ((1 - M.γ) * M.c + M.γ * β) * sl := by
  have : IsProbabilityMeasure M.μ := M.isProb
  unfold Model.G
  have hi : ∫ ε, M.g F s sl d ε ∂M.μ ≤ ∫ _ε, (M.γ * K - ((1 - M.γ) * M.c + M.γ * β) * sl) ∂M.μ := by
    apply integral_mono_ae (g_integrable hLB hs hsl d) (integrable_const _)
    filter_upwards [ae_supp (M := M)] with ε hε
    exact g_le hβc hF hs hsl hd hε
  rw [integral_const] at hi
  simp only [probReal_univ, one_smul] at hi
  linarith [hR d hd]

lemma T_UB (hLB : M.LBp F) (hU : M.UBp F) : M.UBp (M.T F) := by
  obtain ⟨K, β, hβ0, hβc, hF⟩ := hU
  obtain ⟨R, hR⟩ := M.revenue_bdd
  have hγ := M.γ_nonneg
  have hγ1 := M.γ_le_one
  refine ⟨R + M.γ * K, (1 - M.γ) * M.c + M.γ * β, ?_, ?_, ?_⟩
  · have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M.γ) M.c_nonneg
    have := mul_nonneg hγ hβ0
    linarith
  · have := mul_le_mul_of_nonneg_left hβc hγ
    linarith
  · intro y hy
    unfold T
    apply csSup_le ((M.orderSet_ne y).image _)
    rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
    simp only
    have := G_le hLB hβc hF hR hy hsl hd
    have hb : 0 ≤ (1 - M.γ) * M.c + M.γ * β := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M.γ) M.c_nonneg
      have := mul_nonneg hγ hβ0
      linarith
    have := mul_le_mul_of_nonneg_left hsl hb
    linarith

lemma G_bdd (hLB : M.LBp F) (hU : M.UBp F) {s : Fin L → ℝ} (hs : s ∈ V L L) :
    BddAbove ((fun p : ℝ × ℝ => M.G F s p.1 p.2) '' M.orderSet s) := by
  obtain ⟨K, β, hβ0, hβc, hF⟩ := hU
  obtain ⟨R, hR⟩ := M.revenue_bdd
  have hγ := M.γ_nonneg
  have hγ1 := M.γ_le_one
  refine ⟨R + M.γ * K - ((1 - M.γ) * M.c + M.γ * β) * M.sLast s, ?_⟩
  rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
  simp only
  have := G_le hLB hβc hF hR hs hsl hd
  have hb : 0 ≤ (1 - M.γ) * M.c + M.γ * β := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - M.γ) M.c_nonneg
    have := mul_nonneg hγ hβ0
    linarith
  have := mul_le_mul_of_nonneg_left hsl hb
  linarith

/-- The constructed-policy estimate, one period: `g` at `s` vs. at `s + δe`. -/
lemma g_shift (hLB : M.LBp F) {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ}
    (hsl : M.sLast s ≤ sl) (d ε δ : ℝ) (hδ : 0 ≤ δ) :
    M.g F s sl d ε ≤ M.g F (s + δ • (1 : Fin L → ℝ)) (sl + δ) d ε + (M.θ + M.c) * δ := by
  have hs' := V_shift hs δ
  have hsl' : M.sLast (s + δ • (1 : Fin L → ℝ)) ≤ sl + δ := by
    rw [sLast_shift]; linarith
  unfold Model.g
  apply csSup_le ((Set.nonempty_Icc.mpr (lo_le_hi hs hsl d ε)).image _)
  rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
  simp only
  set N := M.netInv s sl with hN
  set dt := d + ε
  set hi1 := max (N + δ) dt
  set a1 := min (a + δ) hi1
  have hdep : a1 ∈ M.depletionSet (s + δ • (1 : Fin L → ℝ)) (sl + δ) d ε := by
    unfold Model.depletionSet
    rw [s1_shift, netInv_shift]
    refine ⟨le_min ?_ ?_, min_le_right _ _⟩
    · apply max_le
      · linarith [le_trans (le_max_left _ _) ha1]
      · linarith [le_trans (le_max_right _ _) ha1]
    · exact max_le_max (by linarith [M.s1_le_netInv hs hsl]) le_rfl
  have hB : BddAbove ((fun a => M.phi F (s + δ • (1 : Fin L → ℝ)) (sl + δ) d a ε) ''
      M.depletionSet (s + δ • (1 : Fin L → ℝ)) (sl + δ) d ε) :=
    (phi_bdd hLB hs' hsl' d ε).mono (Set.image_mono (fun x hx => hx.1))
  refine le_trans ?_ (add_le_add_left (le_csSup hB ⟨a1, hdep, rfl⟩) _)
  simp only
  have haa1 : a ≤ a1 := le_min (by linarith) (le_trans ha2 (max_le_max (by linarith) le_rfl))
  have ha1d : a1 ≤ a + δ := min_le_left _ _
  set δ' := a + δ - a1
  have hnext : Model.next s sl a = Model.next (s + δ • (1 : Fin L → ℝ)) (sl + δ) a1 - δ' • (1 : Fin L → ℝ) := by
    rw [next_shift, next_sub s sl a a1]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, δ']
    ring
  have hF := hLB _ (M.next_mem hs' hsl' a1) δ' (by simp only [δ']; linarith)
  rw [← hnext] at hF
  rw [phi_eq, phi_eq, netInv_shift, ← hN]
  have hp : max (N + δ - a1) 0 = max (N - a) 0 := by
    rcases le_total (a + δ) hi1 with h | h
    · have : a1 = a + δ := min_eq_left h
      rw [this]; congr 1; ring
    · have e : a1 = hi1 := min_eq_right h
      have hNa : N + δ ≤ hi1 := le_max_left _ _
      rw [e, max_eq_right (by linarith), max_eq_right (by linarith)]
  have hm : M.hm * max (a1 - (N + δ)) 0 ≤ M.hm * max (a - N) 0 :=
    mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) M.hm_nonneg
  have hγ := M.γ_nonneg
  have e1 : M.γ * F (Model.next s sl a) ≤
      M.γ * (F (Model.next (s + δ • (1 : Fin L → ℝ)) (sl + δ) a1) + (M.θ + M.c) * δ') :=
    mul_le_mul_of_nonneg_left hF hγ
  have e2 : 0 ≤ (1 - M.γ) * M.θ * δ' :=
    mul_nonneg (mul_nonneg (by linarith [M.γ_le_one]) M.θ_nonneg) (by simp only [δ']; linarith)
  rw [hp]
  simp only [δ'] at e1 e2
  linarith

end Q

end PerishablePricing.Backlog.Model


namespace PerishablePricing.Backlog.Model
open PPBSol MeasureTheory

variable {L k : ℕ} (M : Model L k)

lemma lnat_congr {ι : Type*} {S S' : Set (ι → ℝ)} {f g : (ι → ℝ) → ℝ}
    (h : LNatConcaveOn S f) (hS : S = S') (hfg : ∀ x ∈ S', f x = g x) :
    LNatConcaveOn S' g := by
  subst hS
  rw [lnatConcave_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun u hu v hv α hα => ?_⟩
  rw [← hfg u hu, ← hfg v hv, ← hfg _ (h1 u hu v hv α hα).1, ← hfg _ (h1 u hu v hv α hα).2]
  exact h2 u hu v hv α hα

section Q
variable {M}
variable {F : (Fin L → ℝ) → ℝ}

lemma G_shift (hLB : M.LBp F) {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ}
    (hsl : M.sLast s ≤ sl) (d δ : ℝ) (hδ : 0 ≤ δ) :
    M.G F s sl d ≤ M.G F (s + δ • (1 : Fin L → ℝ)) (sl + δ) d + (M.θ + M.c) * δ := by
  have : IsProbabilityMeasure M.μ := M.isProb
  have hs' := V_shift hs δ
  have hsl' : M.sLast (s + δ • (1 : Fin L → ℝ)) ≤ sl + δ := by
    rw [sLast_shift]; linarith
  unfold Model.G
  have h1 := g_integrable hLB hs hsl d
  have h2 := g_integrable hLB hs' hsl' d
  have hi := integral_mono h1 (h2.add (integrable_const ((M.θ + M.c) * δ)))
    (fun ε => g_shift hLB hs hsl d ε δ hδ)
  simp only [Pi.add_apply] at hi
  rw [integral_add h2 (integrable_const _), integral_const] at hi
  simp only [probReal_univ, one_smul] at hi
  linarith

lemma T_LB (hLB : M.LBp F) (hU : M.UBp F) : M.LBp (M.T F) := by
  intro x hx δ hδ
  set s := x - δ • (1 : Fin L → ℝ)
  have hs : s ∈ V L L := by
    have := V_shift hx (-δ)
    have e : x + (-δ) • (1 : Fin L → ℝ) = s := by simp only [s, neg_smul]; abel
    rwa [e] at this
  have hx' : x = s + δ • (1 : Fin L → ℝ) := by simp only [s]; abel
  rw [hx']
  have hs' := V_shift hs δ
  unfold T
  apply csSup_le ((M.orderSet_ne s).image _)
  rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
  simp only
  have h1 := G_shift hLB hs hsl d δ hδ
  have h2 := le_csSup (G_bdd hLB hU hs') ⟨(sl + δ, d), ⟨by rw [sLast_shift]; linarith, hd⟩, rfl⟩
  simp only at h2
  linarith

end Q

/-! ## Joint vectors -/

/-- `φ` as a function of the joint vector. -/
noncomputable def PhiJ (F : (Fin L → ℝ) → ℝ) (ε : ℝ) (w : Fin (L + 3) → ℝ) : ℝ :=
  M.phi F (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩)
    (w ⟨L + 2, by omega⟩) ε

noncomputable def GJ (F : (Fin L → ℝ) → ℝ) (ε : ℝ) (w : Fin (L + 2) → ℝ) : ℝ :=
  M.g F (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩) ε

noncomputable def GGJ (F : (Fin L → ℝ) → ℝ) (w : Fin (L + 2) → ℝ) : ℝ :=
  M.G F (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 1, by omega⟩)

lemma GGJ_eq (F : (Fin L → ℝ) → ℝ) (w : Fin (L + 2) → ℝ) :
    M.GGJ F w = M.P (w ⟨L + 1, by omega⟩) * w ⟨L + 1, by omega⟩ + ∫ ε, M.GJ F ε w ∂M.μ := rfl

lemma ext_proj {m : ℕ} (hm : L + 1 ≤ m) (w : Fin m → ℝ) (j : Fin (L + 1)) :
    Model.ext (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) j = w ⟨j, by omega⟩ := by
  induction j using Fin.lastCases with
  | last => rw [ext_last]; rfl
  | cast i => rw [ext_castSucc]; rfl

lemma PhiJ_eq (F : (Fin L → ℝ) → ℝ) (ε : ℝ) (w : Fin (L + 3) → ℝ) :
    M.PhiJ F ε w = M.γ * M.c * (w ⟨L, by omega⟩ - w ⟨L + 2, by omega⟩) - M.c * w ⟨L, by omega⟩
      - M.θ * (w ⟨L + 2, by omega⟩ - (w ⟨L + 1, by omega⟩ + ε))
      - M.hp * max (w ⟨L - k, by omega⟩ - w ⟨L + 2, by omega⟩) 0
      - M.hm * max (w ⟨L + 2, by omega⟩ - w ⟨L - k, by omega⟩) 0
      + M.γ * F (fun i : Fin L => w ⟨i.val + 1, by omega⟩ - w ⟨L + 2, by omega⟩) := by
  have hk := M.k_le_L
  unfold PhiJ
  rw [phi_eq]
  have h1 : M.netInv (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) = w ⟨L - k, by omega⟩ :=
    ext_proj (by omega) w ⟨L - k, by omega⟩
  have h2 : Model.next (fun i : Fin L => w ⟨i, by omega⟩) (w ⟨L, by omega⟩) (w ⟨L + 2, by omega⟩)
      = fun i : Fin L => w ⟨i.val + 1, by omega⟩ - w ⟨L + 2, by omega⟩ := by
    funext i
    simp only [Model.next]
    rw [ext_proj (by omega) w i.succ]
    rfl
  rw [h1, h2]

lemma PhiJ_conc {F : (Fin L → ℝ) → ℝ} (hF : LNatConcaveOn (V L L) F) (ε : ℝ) :
    LNatConcaveOn (V (L + 3) (L + 1)) (M.PhiJ F ε) := by
  have hk := M.k_le_L
  rw [lnatConcave_iff] at hF ⊢
  refine ⟨V_lnat _ _, ?_⟩
  intro u hu v hv α hα
  simp only [PhiJ_eq]
  have l1 := lin_eq u v α ⟨L, by omega⟩
  have l2 := lin_eq u v α ⟨L + 1, by omega⟩
  have l3 := lin_eq u v α ⟨L + 2, by omega⟩
  have d1 := diff_ineq u v α ⟨L - k, by omega⟩ ⟨L + 2, by omega⟩
  have d2 := diff_ineq u v α ⟨L + 2, by omega⟩ ⟨L - k, by omega⟩
  have hmem : ∀ w ∈ V (L + 3) (L + 1),
      (fun i : Fin L => w ((fun i : Fin L => (⟨i.val + 1, by omega⟩ : Fin (L + 3))) i)
        - w ⟨L + 2, by omega⟩) ∈ V L L := by
    intro w hw i j hij hj
    simp only
    have := hw ⟨i.val + 1, by omega⟩ ⟨j.val + 1, by omega⟩
      (by rw [Fin.le_def] at hij ⊢; simp only; omega) (by simp only; omega)
    linarith
  have c1 := comp_ineq (V L L) F hF.2 (fun i : Fin L => (⟨i.val + 1, by omega⟩ : Fin (L + 3)))
    ⟨L + 2, by omega⟩ u v α hα (hmem u hu) (hmem v hv)
  try simp only at c1
  have e1 := mul_le_mul_of_nonneg_left d1 M.hp_nonneg
  have e2 := mul_le_mul_of_nonneg_left d2 M.hm_nonneg
  have e3 := mul_le_mul_of_nonneg_left c1 M.γ_nonneg
  have m1 := congrArg (fun t => M.γ * M.c * t) l1
  have m2 := congrArg (fun t => M.c * t) l1
  have m3 := congrArg (fun t => M.θ * t) l2
  have m4 := congrArg (fun t => M.θ * t) l3
  have m5 := congrArg (fun t => M.γ * M.c * t) l3
  try simp only at m1 m2 m3 m4 m5
  linarith

end PerishablePricing.Backlog.Model


namespace PerishablePricing.Backlog.Model
open PPBSol MeasureTheory

variable {L k : ℕ} (M : Model L k)

/-! ### `join3 x a = (x, a)` -/

def join3 (x : Fin (L + 2) → ℝ) (a : ℝ) : Fin (L + 3) → ℝ :=
  fun i => if h : (i : ℕ) < L + 2 then x ⟨i, h⟩ else a

lemma join3_lt (x : Fin (L + 2) → ℝ) (a : ℝ) (i : Fin (L + 3)) (h : (i : ℕ) < L + 2) :
    join3 x a i = x ⟨i, h⟩ := dif_pos h

lemma join3_last (x : Fin (L + 2) → ℝ) (a : ℝ) : join3 x a ⟨L + 2, by omega⟩ = a :=
  dif_neg (by simp)

lemma join3_inf (x x' : Fin (L + 2) → ℝ) (a a' α : ℝ) :
    (join3 x a + α • (1 : Fin (L + 3) → ℝ)) ⊓ join3 x' a' =
      join3 ((x + α • (1 : Fin (L + 2) → ℝ)) ⊓ x') (min (a + α) a') := by
  funext i
  rw [pinf]
  by_cases h : (i : ℕ) < L + 2
  · rw [join3_lt _ _ _ h, join3_lt _ _ _ h, join3_lt _ _ _ h, pinf]
  · simp only [join3, h, dite_false]

lemma join3_sup (x x' : Fin (L + 2) → ℝ) (a a' α : ℝ) :
    join3 x a ⊔ (join3 x' a' - α • (1 : Fin (L + 3) → ℝ)) =
      join3 (x ⊔ (x' - α • (1 : Fin (L + 2) → ℝ))) (max a (a' - α)) := by
  funext i
  rw [psup]
  by_cases h : (i : ℕ) < L + 2
  · rw [join3_lt _ _ _ h, join3_lt _ _ _ h, join3_lt _ _ _ h, psup]
  · simp only [join3, h, dite_false]

/-- The constraint set of `g̃`. -/
def D3 (L : ℕ) (ε : ℝ) : Set (Fin (L + 3) → ℝ) :=
  V (L + 3) (L + 1) ∩ ({w | w ⟨0, by omega⟩ + 0 ≤ w ⟨L + 2, by omega⟩} ∩
    {w | w ⟨L + 1, by omega⟩ + ε ≤ w ⟨L + 2, by omega⟩})

lemma D3_lnat (ε : ℝ) : LNatConvexSet (D3 L ε) :=
  lnatSet_inter (V_lnat _ _) (lnatSet_inter (lnatSet_le _ _ _) (lnatSet_le _ _ _))

lemma join3_V {x : Fin (L + 2) → ℝ} {a : ℝ} (h : join3 x a ∈ V (L + 3) (L + 1)) :
    x ∈ V (L + 2) (L + 1) := by
  intro i j hij hj
  have := h ⟨i, by omega⟩ ⟨j, by omega⟩ (by rw [Fin.le_def] at hij ⊢; simpa using hij)
    (by simpa using hj)
  rwa [join3_lt _ _ _ (by simp), join3_lt _ _ _ (by simp)] at this

lemma D3_section {x : Fin (L + 2) → ℝ} (hx : x ∈ V (L + 2) (L + 1)) (ε : ℝ) :
    {a | join3 x a ∈ D3 L ε} = Set.Ici (max (x ⟨0, by omega⟩) (x ⟨L + 1, by omega⟩ + ε)) := by
  ext a
  simp only [D3, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici, max_le_iff]
  rw [join3_lt _ _ ⟨0, by omega⟩ (by simp), join3_lt _ _ ⟨L + 1, by omega⟩ (by simp), join3_last]
  simp only [add_zero]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    intro i j hij hj
    rw [join3_lt _ _ _ (by omega), join3_lt _ _ _ (by omega)]
    exact hx _ _ (by rw [Fin.le_def] at hij ⊢; simpa using hij) (by simpa using hj)

lemma D3_proj (ε : ℝ) : {x | ∃ a, join3 x a ∈ D3 L ε} = V (L + 2) (L + 1) := by
  ext x
  constructor
  · rintro ⟨a, ha⟩
    exact join3_V ha.1
  · intro hx
    refine ⟨max (x ⟨0, by omega⟩) (x ⟨L + 1, by omega⟩ + ε), ?_⟩
    have := D3_section hx ε
    have h : max (x ⟨0, by omega⟩) (x ⟨L + 1, by omega⟩ + ε) ∈ {a | join3 x a ∈ D3 L ε} := by
      rw [this]; exact Set.mem_Ici.mpr le_rfl
    exact h

lemma pr_mem {m : ℕ} (hm : L + 1 ≤ m) {w : Fin m → ℝ} (hw : w ∈ V m (L + 1)) :
    (fun i : Fin L => w ⟨i, by omega⟩) ∈ V L L ∧
      M.sLast (fun i : Fin L => w ⟨i, by omega⟩) ≤ w ⟨L, by omega⟩ := by
  have hL := M.one_le_L
  constructor
  · intro i j hij hj
    exact hw _ _ (by rw [Fin.le_def] at hij ⊢; simpa using hij) (by simp)
  · exact hw _ _ (by rw [Fin.le_def]; simp) (by simp)

lemma PhiJ_join3 (F : (Fin L → ℝ) → ℝ) (ε : ℝ) (x : Fin (L + 2) → ℝ) (a : ℝ) :
    M.PhiJ F ε (join3 x a) =
      M.phi F (fun i : Fin L => x ⟨i, by omega⟩) (x ⟨L, by omega⟩) (x ⟨L + 1, by omega⟩) a ε := by
  unfold PhiJ
  have e : (fun i : Fin L => join3 x a ⟨i, by omega⟩) = fun i : Fin L => x ⟨i, by omega⟩ := by
    funext i; rw [join3_lt _ _ _ (by simp; omega)]
  rw [e, join3_lt _ _ ⟨L, by omega⟩ (by simp), join3_lt _ _ ⟨L + 1, by omega⟩ (by simp),
    join3_last]

lemma GJ_conc {F : (Fin L → ℝ) → ℝ} (hF : LNatConcaveOn (V L L) F) (hLB : M.LBp F) (ε : ℝ) :
    LNatConcaveOn (V (L + 2) (L + 1)) (M.GJ F ε) := by
  have hP := (lnatConcave_iff _ _).1 (M.PhiJ_conc hF ε)
  have key := partial_sup (D3 L ε) (M.PhiJ F ε) join3 (D3_lnat ε)
    (fun u hu v hv α hα => hP.2 u hu.1 v hv.1 α hα)
    (fun x x' y y' α => ⟨_, _, join3_inf x x' y y' α, join3_sup x x' y y' α⟩)
    (by
      rintro x ⟨a, ha⟩
      have hx := join3_V ha.1
      obtain ⟨hs, hsl⟩ := M.pr_mem (by omega) hx
      rw [D3_section hx ε]
      have e : (fun y => M.PhiJ F ε (join3 x y)) = fun y =>
          M.phi F (fun i : Fin L => x ⟨i, by omega⟩) (x ⟨L, by omega⟩) (x ⟨L + 1, by omega⟩) y ε := by
        funext y; exact M.PhiJ_join3 F ε x y
      rw [e]
      exact phi_bdd hLB hs hsl _ ε)
  refine lnat_congr key (D3_proj ε) ?_
  intro x hx
  obtain ⟨hs, hsl⟩ := M.pr_mem (by omega) hx
  try simp only
  rw [D3_section hx ε]
  have e : (fun y => M.PhiJ F ε (join3 x y)) = fun y =>
      M.phi F (fun i : Fin L => x ⟨i, by omega⟩) (x ⟨L, by omega⟩) (x ⟨L + 1, by omega⟩) y ε := by
    funext y; exact M.PhiJ_join3 F ε x y
  rw [e]
  unfold GJ
  rw [g_eq_gtilde hLB hs hsl]
  rfl

/-! ### `join2 x (sl, d)` -/

def join2 (x : Fin L → ℝ) (y : ℝ × ℝ) : Fin (L + 2) → ℝ :=
  fun i => if h : (i : ℕ) < L then x ⟨i, h⟩ else if (i : ℕ) = L then y.1 else y.2

lemma join2_lt (x : Fin L → ℝ) (y : ℝ × ℝ) (i : Fin (L + 2)) (h : (i : ℕ) < L) :
    join2 x y i = x ⟨i, h⟩ := dif_pos h

lemma join2_L (x : Fin L → ℝ) (y : ℝ × ℝ) : join2 x y ⟨L, by omega⟩ = y.1 := by
  simp [join2]

lemma join2_L1 (x : Fin L → ℝ) (y : ℝ × ℝ) : join2 x y ⟨L + 1, by omega⟩ = y.2 := by
  simp [join2]

lemma join2_inf (x x' : Fin L → ℝ) (y y' : ℝ × ℝ) (α : ℝ) :
    (join2 x y + α • (1 : Fin (L + 2) → ℝ)) ⊓ join2 x' y' =
      join2 ((x + α • (1 : Fin L → ℝ)) ⊓ x') (min (y.1 + α) y'.1, min (y.2 + α) y'.2) := by
  funext i
  rw [pinf]
  by_cases h : (i : ℕ) < L
  · rw [join2_lt _ _ _ h, join2_lt _ _ _ h, join2_lt _ _ _ h, pinf]
  · by_cases h' : (i : ℕ) = L
    · simp [join2, h']
    · simp only [join2, h, h', dite_false, if_false]

lemma join2_sup (x x' : Fin L → ℝ) (y y' : ℝ × ℝ) (α : ℝ) :
    join2 x y ⊔ (join2 x' y' - α • (1 : Fin (L + 2) → ℝ)) =
      join2 (x ⊔ (x' - α • (1 : Fin L → ℝ))) (max y.1 (y'.1 - α), max y.2 (y'.2 - α)) := by
  funext i
  rw [psup]
  by_cases h : (i : ℕ) < L
  · rw [join2_lt _ _ _ h, join2_lt _ _ _ h, join2_lt _ _ _ h, psup]
  · by_cases h' : (i : ℕ) = L
    · simp [join2, h']
    · simp only [join2, h, h', dite_false, if_false]

/-- The constraint set of (4) in joint coordinates. -/
def DG : Set (Fin (L + 2) → ℝ) :=
  V (L + 2) (L + 1) ∩ ({w | M.dlo ≤ w ⟨L + 1, by omega⟩} ∩ {w | w ⟨L + 1, by omega⟩ ≤ M.dhi})

lemma DG_lnat : LNatConvexSet M.DG :=
  lnatSet_inter (V_lnat _ _) (lnatSet_inter (lnatSet_ge _ _) (lnatSet_le' _ _))

lemma join2_V {x : Fin L → ℝ} (hx : x ∈ V L L) {y : ℝ × ℝ} (hy : M.sLast x ≤ y.1) :
    join2 x y ∈ V (L + 2) (L + 1) := by
  have hL := M.one_le_L
  intro i j hij hj
  rw [Fin.le_def] at hij
  by_cases hjL : (j : ℕ) < L
  · rw [join2_lt _ _ _ (by omega), join2_lt _ _ _ hjL]
    exact hx _ _ (by rw [Fin.le_def]; simpa using hij) hjL
  · have hjE : j = ⟨L, by omega⟩ := by ext; simp; omega
    rw [hjE, join2_L]
    by_cases hiL : (i : ℕ) < L
    · rw [join2_lt _ _ _ hiL]
      refine le_trans (hx _ ⟨L - 1, by omega⟩ (by rw [Fin.le_def]; simp; omega) (by simp; omega)) hy
    · have hiE : i = ⟨L, by omega⟩ := by ext; simp; omega
      rw [hiE, join2_L]

lemma pr_join2 (x : Fin L → ℝ) (y : ℝ × ℝ) :
    (fun i : Fin L => join2 x y ⟨i, by omega⟩) = x := by
  funext i
  rw [join2_lt _ _ _ (by simp)]

lemma DG_proj : {x | ∃ y, join2 x y ∈ M.DG} = V L L := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have := (M.pr_mem (by omega) hy.1).1
    rwa [pr_join2] at this
  · intro hx
    refine ⟨(M.sLast x, M.dlo), M.join2_V hx le_rfl, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]; rw [join2_L1]
    · simp only [Set.mem_setOf_eq]; rw [join2_L1]; exact M.dlo_le_dhi

lemma DG_section {x : Fin L → ℝ} (hx : x ∈ V L L) :
    {y | join2 x y ∈ M.DG} = M.orderSet x := by
  ext ⟨sl, d⟩
  simp only [DG, Set.mem_inter_iff, Set.mem_setOf_eq, orderSet, Set.mem_Icc]
  rw [join2_L1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := (M.pr_mem (by omega) h1).2
    rw [pr_join2, join2_L] at this
    exact ⟨this, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨M.join2_V hx h1, h2, h3⟩

lemma GGJ_join2 (F : (Fin L → ℝ) → ℝ) (x : Fin L → ℝ) (y : ℝ × ℝ) :
    M.GGJ F (join2 x y) = M.G F x y.1 y.2 := by
  unfold GGJ
  rw [pr_join2, join2_L, join2_L1]

section R
variable {M}
variable {F : (Fin L → ℝ) → ℝ}

lemma GGJ_ineq (hF : LNatConcaveOn (V L L) F) (hLB : M.LBp F) :
    ∀ u ∈ M.DG, ∀ v ∈ M.DG, ∀ α : ℝ, 0 ≤ α →
      M.GGJ F u + M.GGJ F v ≤ M.GGJ F ((u + α • (1 : Fin (L + 2) → ℝ)) ⊓ v) +
        M.GGJ F (u ⊔ (v - α • (1 : Fin (L + 2) → ℝ))) := by
  intro u hu v hv α hα
  have hp := (M.DG_lnat u hu v hv α hα).1
  have hq := (M.DG_lnat u hu v hv α hα).2
  have hr := concave_pair (fun d => M.P d * d) M.dlo M.dhi M.revenue_concave
    (u ⟨L + 1, by omega⟩) (v ⟨L + 1, by omega⟩) α hα ⟨hu.2.1, hu.2.2⟩ ⟨hv.2.1, hv.2.2⟩
  rw [← pinf, ← psup] at hr
  simp only at hr
  have hint : ∀ w ∈ M.DG, Integrable (fun ε => M.GJ F ε w) M.μ := by
    intro w hw
    obtain ⟨hs, hsl⟩ := M.pr_mem (by omega) hw.1
    exact g_integrable hLB hs hsl _
  have hg := fun ε => ((lnatConcave_iff _ _).1 (M.GJ_conc hF hLB ε)).2 u hu.1 v hv.1 α hα
  have hI : ∫ ε, M.GJ F ε u ∂M.μ + ∫ ε, M.GJ F ε v ∂M.μ ≤
      ∫ ε, M.GJ F ε ((u + α • (1 : Fin (L + 2) → ℝ)) ⊓ v) ∂M.μ +
        ∫ ε, M.GJ F ε (u ⊔ (v - α • (1 : Fin (L + 2) → ℝ))) ∂M.μ := by
    rw [← integral_add (hint u hu) (hint v hv), ← integral_add (hint _ hp) (hint _ hq)]
    exact integral_mono ((hint u hu).add (hint v hv)) ((hint _ hp).add (hint _ hq)) hg
  rw [GGJ_eq, GGJ_eq, GGJ_eq, GGJ_eq]
  linarith

lemma T_conc (hF : LNatConcaveOn (V L L) F) (hLB : M.LBp F) (hU : M.UBp F) :
    LNatConcaveOn (V L L) (M.T F) := by
  have key := partial_sup M.DG (M.GGJ F) join2 M.DG_lnat (GGJ_ineq hF hLB)
    (fun x x' y y' α => ⟨_, _, join2_inf x x' y y' α, join2_sup x x' y y' α⟩)
    (by
      rintro x hx
      have hx' : x ∈ V L L := by rw [← M.DG_proj]; exact hx
      rw [M.DG_section hx']
      have e : (fun y => M.GGJ F (join2 x y)) = fun p : ℝ × ℝ => M.G F x p.1 p.2 := by
        funext y; exact M.GGJ_join2 F x y
      rw [e]
      exact G_bdd hLB hU hx')
  refine lnat_congr key M.DG_proj ?_
  intro x hx
  try simp only
  rw [M.DG_section hx]
  have e : (fun y => M.GGJ F (join2 x y)) = fun p : ℝ × ℝ => M.G F x p.1 p.2 := by
    funext y; exact M.GGJ_join2 F x y
  rw [e]
  rfl

end R

theorem good (n : ℕ) : LNatConcaveOn (V L L) (M.f n) ∧ M.LBp (M.f n) ∧ M.UBp (M.f n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [lnatConcave_iff]
      exact ⟨V_lnat _ _, fun _ _ _ _ _ _ => by simp [Model.f]⟩
    · intro x _ δ hδ
      simp only [Model.f]
      have := mul_nonneg (add_nonneg M.θ_nonneg M.c_nonneg) hδ
      linarith
    · exact ⟨0, 0, le_rfl, M.c_nonneg, fun y _ => by simp [Model.f]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [f_succ]
    exact ⟨T_conc h1 h2 h3, T_LB h2 h3, T_UB h2 h3⟩

end PerishablePricing.Backlog.Model


namespace PerishablePricing.Backlog.Model
open PPBSol MeasureTheory

variable {L k : ℕ} (M : Model L k)

lemma join3_V' {x : Fin (L + 2) → ℝ} (hx : x ∈ V (L + 2) (L + 1)) (a : ℝ) :
    join3 x a ∈ V (L + 3) (L + 1) := by
  intro i j hij hj
  rw [join3_lt _ _ _ (by omega), join3_lt _ _ _ (by omega)]
  exact hx _ _ (by rw [Fin.le_def] at hij ⊢; simpa using hij) (by simpa using hj)

lemma PhiJ_J4 (F : (Fin L → ℝ) → ℝ) (ε : ℝ) (s : Fin L → ℝ) (sl d a : ℝ) :
    M.PhiJ F ε (join3 (join2 s (sl, d)) a) = M.phi F s sl d a ε := by
  rw [PhiJ_join3, pr_join2, join2_L, join2_L1]

lemma J4_inf (s s' : Fin L → ℝ) (sl sl' d d' a a' α : ℝ) :
    (join3 (join2 s (sl, d)) a + α • (1 : Fin (L + 3) → ℝ)) ⊓ join3 (join2 s' (sl', d')) a' =
      join3 (join2 ((s + α • (1 : Fin L → ℝ)) ⊓ s') (min (sl + α) sl', min (d + α) d'))
        (min (a + α) a') := by
  rw [join3_inf, join2_inf]

lemma J4_sup (s s' : Fin L → ℝ) (sl sl' d d' a a' α : ℝ) :
    join3 (join2 s (sl, d)) a ⊔ (join3 (join2 s' (sl', d')) a' - α • (1 : Fin (L + 3) → ℝ)) =
      join3 (join2 (s ⊔ (s' - α • (1 : Fin L → ℝ))) (max sl (sl' - α), max d (d' - α)))
        (max a (a' - α)) := by
  rw [join3_sup, join2_sup]

section S
variable {M}
variable {F : (Fin L → ℝ) → ℝ}

lemma phi_le_g (hLB : M.LBp F) {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ}
    (hsl : M.sLast s ≤ sl) (d ε x : ℝ) (hx : max (M.s1 s) (d + ε) ≤ x) :
    M.phi F s sl d x ε ≤ M.g F s sl d ε := by
  rw [g_eq_gtilde hLB hs hsl]
  exact le_csSup (phi_bdd hLB hs hsl d ε) ⟨x, hx, rfl⟩

lemma G_le_T (hLB : M.LBp F) (hU : M.UBp F) {s : Fin L → ℝ} (hs : s ∈ V L L) {sl d : ℝ}
    (h : (sl, d) ∈ M.orderSet s) : M.G F s sl d ≤ M.T F s :=
  le_csSup (G_bdd hLB hU hs) ⟨(sl, d), h, rfl⟩

end S

lemma J4_mem {s : Fin L → ℝ} (hs : s ∈ V L L) {sl : ℝ} (hsl : M.sLast s ≤ sl) (d a : ℝ) :
    join3 (join2 s (sl, d)) a ∈ V (L + 3) (L + 1) :=
  join3_V' (M.join2_V hs hsl) a

lemma s1_mono {s s' : Fin L → ℝ} (h : s ≤ s') : M.s1 s ≤ M.s1 s' := h _

lemma sLast_mono {s s' : Fin L → ℝ} (h : s ≤ s') : M.sLast s ≤ M.sLast s' := h _

theorem main :
    (∀ n : ℕ, LNatConcaveOn (V L L) (M.f n)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 2) (L + 1)) (M.gJoint n ε)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 3) (L + 1)) (M.phiJoint n ε)) ∧
    (∀ (n : ℕ) (s s' : Fin L → ℝ) (S D S' D' : ℝ),
      s ∈ Model.StateSpace L → s' ∈ Model.StateSpace L → s ≤ s' →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n s' S' D' →
      S ≤ S' ∧ D ≤ D' ∧ M.P D' ≤ M.P D) ∧
    (∀ (n : ℕ) (s : Fin L → ℝ) (ω S D S' D' : ℝ),
      s ∈ Model.StateSpace L → 0 ≤ ω →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n (s + ω • (1 : Fin L → ℝ)) S' D' →
      S' ≤ S + ω ∧ D' ≤ D + ω) ∧
    (∀ (n : ℕ) (ε : ℝ) (s s' : Fin L → ℝ) (sl sl' d d' a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl →
      s' ∈ Model.StateSpace L → M.sLast s' ≤ sl' →
      s ≤ s' → sl ≤ sl' → d ≤ d' →
      M.IsLargestOptDepletion n s sl d ε a → M.IsLargestOptDepletion n s' sl' d' ε a' →
      a ≤ a') ∧
    (∀ (n : ℕ) (ε : ℝ) (s : Fin L → ℝ) (sl d ω a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl → 0 ≤ ω →
      M.IsLargestOptDepletion n s sl d ε a →
      M.IsLargestOptDepletion n (s + ω • (1 : Fin L → ℝ)) (sl + ω) (d + ω) ε a' →
      a' ≤ a + ω) := by
  refine ⟨fun n => (M.good n).1, fun n ε => M.GJ_conc (M.good n).1 (M.good n).2.1 ε,
    fun n ε => M.PhiJ_conc (M.good n).1 ε, ?_, ?_, ?_, ?_⟩
  · intro n s s' S D S' D' hs hs' hss' hopt hopt'
    obtain ⟨h1, h2, h3⟩ := M.good n
    have hu : join2 s (S, D) ∈ M.DG := by
      have := hopt.1.1; rw [← M.DG_section hs] at this; exact this
    have hv : join2 s' (S', D') ∈ M.DG := by
      have := hopt'.1.1; rw [← M.DG_section hs'] at this; exact this
    have key := GGJ_ineq h1 h2 _ hu _ hv 0 le_rfl
    rw [join2_inf, join2_sup] at key
    simp only [zero_smul, add_zero, sub_zero, inf_of_le_left hss', sup_of_le_right hss'] at key
    rw [GGJ_join2, GGJ_join2, GGJ_join2, GGJ_join2] at key
    simp only at key
    have eS := hopt.1.2
    have eS' := hopt'.1.2
    unfold Model.GN at eS eS'
    rw [f_succ] at eS eS'
    obtain ⟨⟨⟨hS, hD1, hD2⟩, _⟩, _⟩ := id hopt
    obtain ⟨⟨⟨hS', hD1', hD2'⟩, _⟩, _⟩ := id hopt'
    have hmem1 : (min S S', min D D') ∈ M.orderSet s :=
      ⟨le_min hS (le_trans (M.sLast_mono hss') hS'), le_min hD1 hD1',
        le_trans (min_le_left _ _) hD2⟩
    have hmem2 : (max S S', max D D') ∈ M.orderSet s' :=
      ⟨le_trans hS' (le_max_right _ _), le_trans hD1' (le_max_right _ _), max_le hD2 hD2'⟩
    have b1 := G_le_T h2 h3 hs hmem1
    have b2 := G_le_T h2 h3 hs' hmem2
    have hopt2 : M.IsOptOrder n s' (max S S') (max D D') := by
      refine ⟨hmem2, ?_⟩
      unfold Model.GN
      rw [f_succ]
      linarith
    obtain ⟨c1, c2⟩ := hopt'.2 _ _ hopt2
    have hSS : S ≤ S' := le_trans (le_max_left _ _) c1
    have hDD : D ≤ D' := le_trans (le_max_left _ _) c2
    exact ⟨hSS, hDD, M.P_strictAnti.antitoneOn ⟨hD1, hD2⟩ ⟨hD1', hD2'⟩ hDD⟩
  · intro n s ω S D S' D' hs hω hopt hopt'
    obtain ⟨h1, h2, h3⟩ := M.good n
    have hs' : s + ω • (1 : Fin L → ℝ) ∈ V L L := V_shift hs ω
    have hu : join2 s (S, D) ∈ M.DG := by
      have := hopt.1.1; rw [← M.DG_section hs] at this; exact this
    have hv : join2 (s + ω • (1 : Fin L → ℝ)) (S', D') ∈ M.DG := by
      have := hopt'.1.1; rw [← M.DG_section hs'] at this; exact this
    have key := GGJ_ineq h1 h2 _ hu _ hv ω hω
    rw [join2_inf, join2_sup] at key
    simp only [inf_idem, add_sub_cancel_right, sup_idem] at key
    rw [GGJ_join2, GGJ_join2, GGJ_join2, GGJ_join2] at key
    simp only at key
    have eS := hopt.1.2
    have eS' := hopt'.1.2
    unfold Model.GN at eS eS'
    rw [f_succ] at eS eS'
    obtain ⟨⟨⟨hS, hD1, hD2⟩, _⟩, _⟩ := id hopt
    obtain ⟨⟨⟨hS', hD1', hD2'⟩, _⟩, _⟩ := id hopt'
    rw [sLast_shift] at hS'
    have hmem1 : (min (S + ω) S', min (D + ω) D') ∈ M.orderSet (s + ω • (1 : Fin L → ℝ)) := by
      refine ⟨?_, le_min (by linarith) hD1', le_trans (min_le_right _ _) hD2'⟩
      show M.sLast (s + ω • (1 : Fin L → ℝ)) ≤ min (S + ω) S'
      rw [sLast_shift]; exact le_min (by linarith) hS'
    have hmem2 : (max S (S' - ω), max D (D' - ω)) ∈ M.orderSet s :=
      ⟨le_trans hS (le_max_left _ _), le_trans hD1 (le_max_left _ _),
        max_le hD2 (by linarith)⟩
    have b1 := G_le_T h2 h3 hs' hmem1
    have b2 := G_le_T h2 h3 hs hmem2
    have hopt2 : M.IsOptOrder n s (max S (S' - ω)) (max D (D' - ω)) := by
      refine ⟨hmem2, ?_⟩
      unfold Model.GN
      rw [f_succ]
      linarith
    obtain ⟨c1, c2⟩ := hopt.2 _ _ hopt2
    exact ⟨by linarith [le_max_right S (S' - ω)], by linarith [le_max_right D (D' - ω)]⟩
  · intro n ε s s' sl sl' d d' a a' hs hsl hs' hsl' hss' hsl2 hdd' ha ha'
    obtain ⟨h1, h2, h3⟩ := M.good n
    have hP := ((lnatConcave_iff _ _).1 (M.PhiJ_conc h1 ε)).2
    have key := hP _ (M.J4_mem hs hsl d a) _ (M.J4_mem hs' hsl' d' a') 0 le_rfl
    rw [J4_inf, J4_sup] at key
    simp only [zero_smul, add_zero, sub_zero, inf_of_le_left hss', sup_of_le_right hss',
      min_eq_left hsl2, max_eq_right hsl2, min_eq_left hdd', max_eq_right hdd'] at key
    rw [PhiJ_J4, PhiJ_J4, PhiJ_J4, PhiJ_J4] at key
    obtain ⟨⟨⟨hlo, hhi⟩, e1⟩, _⟩ := ha
    obtain ⟨⟨⟨hlo', hhi'⟩, e2⟩, hgr'⟩ := ha'
    unfold Model.phiN Model.gN at e1 e2
    have hlo2 : max (M.s1 s) (d + ε) ≤ min a a' := by
      refine le_min hlo (le_trans (max_le_max (M.s1_mono hss') (by linarith)) hlo')
    have b1 := phi_le_g h2 hs hsl d ε _ hlo2
    have hdep : max a a' ∈ M.depletionSet s' sl' d' ε := by
      refine ⟨le_trans hlo' (le_max_right _ _), max_le (le_trans hhi ?_) hhi'⟩
      exact max_le_max (M.netInv_mono hss' hsl2) (by linarith)
    have b2 : M.phi (M.f n) s' sl' d' (max a a') ε ≤ M.g (M.f n) s' sl' d' ε :=
      phi_le_g h2 hs' hsl' d' ε _ hdep.1
    have hopt : M.IsOptDepletion n s' sl' d' ε (max a a') := by
      refine ⟨hdep, ?_⟩
      unfold Model.phiN Model.gN
      linarith
    exact le_trans (le_max_left _ _) (hgr' hopt)
  · intro n ε s sl d ω a a' hs hsl hω ha ha'
    obtain ⟨h1, h2, h3⟩ := M.good n
    have hs' : s + ω • (1 : Fin L → ℝ) ∈ V L L := V_shift hs ω
    have hsl' : M.sLast (s + ω • (1 : Fin L → ℝ)) ≤ sl + ω := by rw [sLast_shift]; linarith
    have hP := ((lnatConcave_iff _ _).1 (M.PhiJ_conc h1 ε)).2
    have key := hP _ (M.J4_mem hs hsl d a) _ (M.J4_mem hs' hsl' (d + ω) a') ω hω
    rw [J4_inf, J4_sup] at key
    simp only [inf_idem, add_sub_cancel_right, sup_idem] at key
    rw [PhiJ_J4, PhiJ_J4, PhiJ_J4, PhiJ_J4] at key
    obtain ⟨⟨⟨hlo, hhi⟩, e1⟩, hgr⟩ := ha
    obtain ⟨⟨⟨hlo', hhi'⟩, e2⟩, _⟩ := ha'
    unfold Model.phiN Model.gN at e1 e2
    rw [s1_shift] at hlo'
    rw [netInv_shift] at hhi'
    have hlo2 : max (M.s1 (s + ω • (1 : Fin L → ℝ))) (d + ω + ε) ≤ min (a + ω) a' := by
      rw [s1_shift]
      refine le_min ?_ hlo'
      have := max_le_iff.mp hlo
      exact max_le (by linarith) (by linarith)
    have b1 := phi_le_g h2 hs' hsl' (d + ω) ε _ hlo2
    have hdep : max a (a' - ω) ∈ M.depletionSet s sl d ε := by
      refine ⟨le_trans hlo (le_max_left _ _), max_le hhi ?_⟩
      have := max_le_iff.mp (le_refl (max (M.netInv s sl + ω) (d + ω + ε)))
      have h' : max (M.netInv s sl + ω) (d + ω + ε) = max (M.netInv s sl) (d + ε) + ω := by
        rw [show d + ω + ε = (d + ε) + ω by ring, max_add_add_right]
      linarith
    have b2 : M.phi (M.f n) s sl d (max a (a' - ω)) ε ≤ M.g (M.f n) s sl d ε :=
      phi_le_g h2 hs hsl d ε _ hdep.1
    have hopt : M.IsOptDepletion n s sl d ε (max a (a' - ω)) := by
      refine ⟨hdep, ?_⟩
      unfold Model.phiN Model.gN
      linarith
    have := hgr hopt
    linarith [le_max_right a (a' - ω)]

end PerishablePricing.Backlog.Model

open PerishablePricing.Backlog in
theorem solution {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) :
    (∀ n : ℕ, LNatConcaveOn (V L L) (M.f n)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 2) (L + 1)) (M.gJoint n ε)) ∧
    (∀ (n : ℕ) (ε : ℝ), LNatConcaveOn (V (L + 3) (L + 1)) (M.phiJoint n ε)) ∧
    (∀ (n : ℕ) (s s' : Fin L → ℝ) (S D S' D' : ℝ),
      s ∈ Model.StateSpace L → s' ∈ Model.StateSpace L → s ≤ s' →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n s' S' D' →
      S ≤ S' ∧ D ≤ D' ∧ M.P D' ≤ M.P D) ∧
    (∀ (n : ℕ) (s : Fin L → ℝ) (ω S D S' D' : ℝ),
      s ∈ Model.StateSpace L → 0 ≤ ω →
      M.IsLargestOptOrder n s S D → M.IsLargestOptOrder n (s + ω • (1 : Fin L → ℝ)) S' D' →
      S' ≤ S + ω ∧ D' ≤ D + ω) ∧
    (∀ (n : ℕ) (ε : ℝ) (s s' : Fin L → ℝ) (sl sl' d d' a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl →
      s' ∈ Model.StateSpace L → M.sLast s' ≤ sl' →
      s ≤ s' → sl ≤ sl' → d ≤ d' →
      M.IsLargestOptDepletion n s sl d ε a → M.IsLargestOptDepletion n s' sl' d' ε a' →
      a ≤ a') ∧
    (∀ (n : ℕ) (ε : ℝ) (s : Fin L → ℝ) (sl d ω a a' : ℝ),
      s ∈ Model.StateSpace L → M.sLast s ≤ sl → 0 ≤ ω →
      M.IsLargestOptDepletion n s sl d ε a →
      M.IsLargestOptDepletion n (s + ω • (1 : Fin L → ℝ)) (sl + ω) (d + ω) ε a' →
      a' ≤ a + ω) :=
  M.main
