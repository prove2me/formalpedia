-- Prove2me | solution 1 for ShapiroSDDP.Convergence.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:49:03.835952+00:00
-- url     : https://prove2.me/submissions/0eaddef0-5a1c-4913-a639-0ccadcae2073

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_LinearOptimization_farkas_inequality_form_fintype

open Matrix

namespace SDDPAux
open ShapiroSDDP.Convergence

variable {n m : ℕ}

abbrev CIdx (n m : ℕ) (C : Finset (ℝ × (Fin n → ℝ))) := Fin n ⊕ (Fin m ⊕ (Fin m ⊕ C))

def rowV (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ))) :
    CIdx n m C → Fin n → ℝ
  | Sum.inl i => -(Pi.single i 1)
  | Sum.inr (Sum.inl r) => A r
  | Sum.inr (Sum.inr (Sum.inl r)) => -(A r)
  | Sum.inr (Sum.inr (Sum.inr a)) => (a : ℝ × (Fin n → ℝ)).2

def rowW (C : Finset (ℝ × (Fin n → ℝ))) : CIdx n m C → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr _)) => -1

def rhsG (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ))) : CIdx n m C → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl r) => h r
  | Sum.inr (Sum.inr (Sum.inl r)) => -(h r)
  | Sum.inr (Sum.inr (Sum.inr a)) => -(a : ℝ × (Fin n → ℝ)).1

def snoc' (v : Fin n → ℝ) (w : ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) v w

lemma snoc'_castSucc (v : Fin n → ℝ) (w : ℝ) (k : Fin n) : snoc' v w k.castSucc = v k := by
  simp [snoc']

lemma snoc'_last (v : Fin n → ℝ) (w : ℝ) : snoc' v w (Fin.last n) = w := by
  simp [snoc']

lemma snoc'_dot (v y : Fin n → ℝ) (w t : ℝ) : snoc' v w ⬝ᵥ snoc' y t = v ⬝ᵥ y + w * t := by
  simp [dotProduct, Fin.sum_univ_castSucc, snoc'_castSucc, snoc'_last]

lemma snoc'_init (x : Fin (n + 1) → ℝ) : snoc' (fun k => x k.castSucc) (x (Fin.last n)) = x := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [snoc'_last]
  · simp [snoc'_castSucc]

def Gm (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ))) :
    Matrix (CIdx n m C) (Fin (n + 1)) ℝ :=
  Matrix.of fun i => snoc' (rowV A C i) (rowW C i)

lemma Gm_mulVec (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (y : Fin n → ℝ) (t : ℝ) (i : CIdx n m C) :
    (Gm A C *ᵥ snoc' y t) i = rowV A C i ⬝ᵥ y + rowW C i * t := by
  simp only [mulVec, Gm, Matrix.of_apply]
  exact snoc'_dot _ _ _ _

lemma feas_iff (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (y : Fin n → ℝ) (t : ℝ) :
    Gm A C *ᵥ snoc' y t ≤ rhsG h C ↔ (y, t) ∈ CutLPFeas A h C := by
  constructor
  · intro H
    have H' : ∀ i, rowV A C i ⬝ᵥ y + rowW C i * t ≤ rhsG h C i := fun i => by
      rw [← Gm_mulVec]; exact H i
    refine ⟨fun k => ?_, ?_, fun a ha => ?_⟩
    · have := H' (Sum.inl k)
      simp [rowV, rowW, rhsG] at this
      simpa using this
    · funext r
      have h1 := H' (Sum.inr (Sum.inl r))
      have h2 := H' (Sum.inr (Sum.inr (Sum.inl r)))
      simp [rowV, rowW, rhsG] at h1 h2
      simp only [mulVec]
      change A r ⬝ᵥ y = h r
      linarith
    · have := H' (Sum.inr (Sum.inr (Sum.inr ⟨a, ha⟩)))
      simp [rowV, rowW, rhsG] at this
      simp only [cutEval]
      linarith
  · rintro ⟨hy, hA, hC⟩ i
    rw [Gm_mulVec]
    have hAr : ∀ r, A r ⬝ᵥ y = h r := fun r => congrFun hA r
    rcases i with k | r | r | ⟨a, ha⟩
    · simp [rowV, rowW, rhsG]; exact hy k
    · simp [rowV, rowW, rhsG, hAr]
    · simp [rowV, rowW, rhsG, hAr]
    · have := hC a ha
      simp only [cutEval] at this
      simp [rowV, rowW, rhsG]
      linarith

lemma weak_duality (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) (d : CutDual m C)
    (hd : d ∈ CutDualFeas A C c) (q : (Fin n → ℝ) × ℝ) (hq : q ∈ CutLPFeas A h C) :
    cutDualObj h C d ≤ cutLPObj c q := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  obtain ⟨hy, hA, hC⟩ := hq
  have e1 : (Aᵀ *ᵥ d.1 - ∑ a : C, d.2 a • (a : ℝ × (Fin n → ℝ)).2) ⬝ᵥ q.1 ≤ c ⬝ᵥ q.1 :=
    dotProduct_le_dotProduct_of_nonneg_right hd1 hy
  have e2 : (Aᵀ *ᵥ d.1) ⬝ᵥ q.1 = d.1 ⬝ᵥ h := by
    rw [mulVec_transpose, ← dotProduct_mulVec, hA]
  have e3 : (∑ a : C, d.2 a • (a : ℝ × (Fin n → ℝ)).2) ⬝ᵥ q.1 =
      ∑ a : C, d.2 a * ((a : ℝ × (Fin n → ℝ)).2 ⬝ᵥ q.1) := by
    rw [sum_dotProduct]; simp [smul_dotProduct]
  have e4 : ∑ a : C, d.2 a * ((a : ℝ × (Fin n → ℝ)).2 ⬝ᵥ q.1) ≤
      ∑ a : C, d.2 a * (q.2 - (a : ℝ × (Fin n → ℝ)).1) := by
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (hd3 a)
    have := hC a a.2
    simp only [cutEval] at this
    linarith
  have e5 : ∑ a : C, d.2 a * (q.2 - (a : ℝ × (Fin n → ℝ)).1) =
      q.2 - ∑ a : C, d.2 a * (a : ℝ × (Fin n → ℝ)).1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd2, one_mul]
  rw [sub_dotProduct, e2, e3] at e1
  simp only [cutDualObj, cutLPObj]
  linarith


lemma Gm_transpose_castSucc (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (y : CIdx n m C → ℝ) (k : Fin n) :
    ((Gm A C)ᵀ *ᵥ y) k.castSucc = -(y (Sum.inl k)) + ∑ r, A r k * y (Sum.inr (Sum.inl r))
      - ∑ r, A r k * y (Sum.inr (Sum.inr (Sum.inl r)))
      + ∑ a : C, (a : ℝ × (Fin n → ℝ)).2 k * y (Sum.inr (Sum.inr (Sum.inr a))) := by
  simp only [mulVec, dotProduct, transpose_apply, Gm, Matrix.of_apply, snoc'_castSucc,
    Fintype.sum_sum_type, rowV]
  simp [Pi.single_apply, Finset.sum_neg_distrib]
  ring

lemma Gm_transpose_last (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (y : CIdx n m C → ℝ) :
    ((Gm A C)ᵀ *ᵥ y) (Fin.last n) = -∑ a : C, y (Sum.inr (Sum.inr (Sum.inr a))) := by
  simp only [mulVec, dotProduct, transpose_apply, Gm, Matrix.of_apply, snoc'_last,
    Fintype.sum_sum_type, rowW]
  simp

lemma rhsG_dot (h : Fin m → ℝ) (C : Finset (ℝ × (Fin n → ℝ))) (y : CIdx n m C → ℝ) :
    rhsG h C ⬝ᵥ y = ∑ r, h r * y (Sum.inr (Sum.inl r)) - ∑ r, h r * y (Sum.inr (Sum.inr (Sum.inl r)))
      - ∑ a : C, (a : ℝ × (Fin n → ℝ)).1 * y (Sum.inr (Sum.inr (Sum.inr a))) := by
  simp only [dotProduct, Fintype.sum_sum_type, rhsG]
  simp [Finset.sum_neg_distrib]
  ring

/-- Strong duality and attainment for the cut LP. -/
theorem cutLP_strong (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) (hf : CutLPFinite A h C c) :
    ∃ p, IsCutLPOpt A h C c p ∧ ∃ d ∈ CutDualFeas A C c, cutDualObj h C d = cutLPObj c p := by
  classical
  obtain ⟨⟨p0, hp0⟩, ⟨L, hL⟩⟩ := hf
  set o : Fin (n + 1) → ℝ := -snoc' c 1 with ho
  have hobj : ∀ y t, o ⬝ᵥ snoc' y t = -cutLPObj c (y, t) := by
    intro y t
    rw [ho, neg_dotProduct, snoc'_dot]; simp [cutLPObj]
  have hfeas : ∃ x, Gm A C *ᵥ x ≤ rhsG h C :=
    ⟨snoc' p0.1 p0.2, (feas_iff A h C p0.1 p0.2).2 hp0⟩
  have hbd : ∀ x : Fin (n + 1) → ℝ, (Gm A C).mulVec x ≤ rhsG h C → o ⬝ᵥ x ≤ -L := by
    intro x hx
    rw [← snoc'_init x] at hx ⊢
    rw [hobj]
    have := hL ⟨_, (feas_iff A h C _ _).1 hx, rfl⟩
    linarith
  obtain ⟨p, hp0', hpT, -⟩ :=
    (LinearOptimization.farkas_inequality_form_fintype (Gm A C) (rhsG h C) o (-L) hfeas).1 hbd
  obtain ⟨x, y, hx, hy0, hyT, heq, hopt⟩ :=
    LP.strong_duality_matrix (Gm A C) (rhsG h C) o hfeas ⟨p, hp0', hpT⟩
  refine ⟨(fun k => x k.castSucc, x (Fin.last n)), ⟨?_, ?_⟩, ?_⟩
  · rw [← feas_iff, snoc'_init]; exact hx
  · intro q hq
    have h1 := hopt (snoc' q.1 q.2) ((feas_iff A h C _ _).2 hq)
    rw [← snoc'_init x, hobj, hobj] at h1
    linarith
  · refine ⟨(fun r => y (Sum.inr (Sum.inr (Sum.inl r))) - y (Sum.inr (Sum.inl r)),
      fun a => y (Sum.inr (Sum.inr (Sum.inr a)))), ⟨?_, ?_, fun a => hy0 _⟩, ?_⟩
    · intro k
      have hk := congrFun hyT k.castSucc
      rw [Gm_transpose_castSucc, ho] at hk
      simp only [Pi.neg_apply, snoc'_castSucc] at hk
      have hμ := hy0 (Sum.inl k)
      simp only [Pi.sub_apply, mulVec, dotProduct, transpose_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      simp only [Pi.zero_apply] at hμ
      have : ∑ a : C, y (Sum.inr (Sum.inr (Sum.inr a))) * (a : ℝ × (Fin n → ℝ)).2 k =
          ∑ a : C, (a : ℝ × (Fin n → ℝ)).2 k * y (Sum.inr (Sum.inr (Sum.inr a))) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      linarith
    · have hk := congrFun hyT (Fin.last n)
      rw [Gm_transpose_last, ho] at hk
      simp only [Pi.neg_apply, snoc'_last] at hk
      linarith
    · have h2 : o ⬝ᵥ x = -cutLPObj c (fun k => x k.castSucc, x (Fin.last n)) := by
        conv_lhs => rw [← snoc'_init x]
        exact hobj _ _
      rw [heq, rhsG_dot] at h2
      simp only [cutDualObj, dotProduct, sub_mul, Finset.sum_sub_distrib]
      have e1 : ∑ r, y (Sum.inr (Sum.inr (Sum.inl r))) * h r = ∑ r, h r * y (Sum.inr (Sum.inr (Sum.inl r))) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      have e2 : ∑ r, y (Sum.inr (Sum.inl r)) * h r = ∑ r, h r * y (Sum.inr (Sum.inl r)) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      have e3 : ∑ a : C, y (Sum.inr (Sum.inr (Sum.inr a))) * (a : ℝ × (Fin n → ℝ)).1 =
          ∑ a : C, (a : ℝ × (Fin n → ℝ)).1 * y (Sum.inr (Sum.inr (Sum.inr a))) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [e1, e2, e3]
      linarith

theorem attainment' {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) (hfin : CutLPFinite A h C c) :
    ∃ p, IsCutLPOpt A h C c p := by
  obtain ⟨p, hp, -⟩ := cutLP_strong A h C c hfin
  exact ⟨p, hp⟩


/-- A polyhedron `{x | f i x ≤ b i}` (finitely many affine constraints) has finitely many
extreme points: an extreme point is determined by its set of active constraints. -/
theorem extremePoints_finite_of_ineq {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*}
    [Finite ι] (f : ι → V → ℝ) (b : ι → ℝ)
    (hf : ∀ i x y (s : ℝ), f i (x + s • (x - y)) = f i x + s * (f i x - f i y)) :
    (Set.extremePoints ℝ {x | ∀ i, f i x ≤ b i}).Finite := by
  classical
  set S := {x | ∀ i, f i x ≤ b i}
  let φ : V → Set ι := fun x => {i | f i x = b i}
  have hinj : Set.InjOn φ (Set.extremePoints ℝ S) := by
    intro x hx y hy hxy
    have hxS : x ∈ S := hx.1
    have hyS : y ∈ S := hy.1
    have hact : ∀ i, f i x = b i ↔ f i y = b i := by
      intro i
      have := congrArg (fun T : Set ι => i ∈ T) hxy
      simpa [φ] using this
    have hev : ∀ᶠ ε in nhds (0 : ℝ), ∀ i, f i x < b i → f i x + ε * (f i x - f i y) < b i := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : f i x < b i
      · have hc : ContinuousAt (fun ε : ℝ => f i x + ε * (f i x - f i y)) 0 :=
          (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
        have := hc.eventually_lt continuousAt_const (by simpa using hi)
        exact this.mono (fun ε hε _ => hε)
      · exact Filter.Eventually.of_forall (fun ε h => absurd h hi)
    obtain ⟨ε, hε, hεpos⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)))).exists
    set z := x + ε • (x - y) with hz
    have hzS : z ∈ S := by
      intro i
      rw [hz, hf]
      rcases (hxS i).lt_or_eq with hlt | heq
      · exact (hε i hlt).le
      · have := (hact i).1 heq
        rw [heq, this]; simp
    have hseg : x ∈ openSegment ℝ y z := by
      refine ⟨ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity, by field_simp; ring, ?_⟩
      rw [hz]
      have h1 : (1 + ε) ≠ 0 := by positivity
      simp only [smul_add, smul_sub, smul_smul]
      have : (ε / (1 + ε)) • y + ((1 / (1 + ε)) • x + ((1 / (1 + ε) * ε) • x - (1 / (1 + ε) * ε) • y))
          = ((1 / (1 + ε)) + (1 / (1 + ε) * ε)) • x + ((ε / (1 + ε)) - (1 / (1 + ε) * ε)) • y := by
        simp only [add_smul, sub_smul]; abel
      rw [this]
      have e1 : (1 / (1 + ε)) + (1 / (1 + ε) * ε) = 1 := by field_simp
      have e2 : (ε / (1 + ε)) - (1 / (1 + ε) * ε) = 0 := by field_simp; ring
      rw [e1, e2]; simp
    exact (hx.2 hyS hzS hseg).symm
  have hfin : (φ '' Set.extremePoints ℝ S).Finite := Set.toFinite _
  exact hfin.of_finite_image hinj

/-- The dual feasible region as a polyhedron given by finitely many affine inequalities. -/
def dualF (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ))) :
    (Fin n ⊕ (Bool ⊕ C)) → CutDual m C → ℝ
  | Sum.inl k, d => (Aᵀ *ᵥ d.1 - ∑ a : C, d.2 a • (a : ℝ × (Fin n → ℝ)).2) k
  | Sum.inr (Sum.inl true), d => ∑ a : C, d.2 a
  | Sum.inr (Sum.inl false), d => -∑ a : C, d.2 a
  | Sum.inr (Sum.inr a), d => -d.2 a

def dualB (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) : (Fin n ⊕ (Bool ⊕ C)) → ℝ
  | Sum.inl k => c k
  | Sum.inr (Sum.inl true) => 1
  | Sum.inr (Sum.inl false) => -1
  | Sum.inr (Sum.inr _) => 0

lemma dualFeas_eq (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (c : Fin n → ℝ) : CutDualFeas A C c = {d | ∀ i, dualF A C i d ≤ dualB C c i} := by
  ext d
  simp only [CutDualFeas, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    rcases i with k | (_ | _) | a
    · exact h1 k
    · simp only [dualF, dualB]; linarith
    · simp only [dualF, dualB]; linarith
    · simpa [dualF, dualB] using h3 a
  · intro H
    refine ⟨fun k => H (Sum.inl k), ?_, fun a => ?_⟩
    · have h1 := H (Sum.inr (Sum.inl true))
      have h2 := H (Sum.inr (Sum.inl false))
      simp only [dualF, dualB] at h1 h2
      linarith
    · have := H (Sum.inr (Sum.inr a))
      simp only [dualF, dualB] at this
      linarith

theorem dual_extremePoints_finite (A : Matrix (Fin m) (Fin n) ℝ) (C : Finset (ℝ × (Fin n → ℝ)))
    (c : Fin n → ℝ) : (Set.extremePoints ℝ (CutDualFeas A C c)).Finite := by
  rw [dualFeas_eq]
  apply extremePoints_finite_of_ineq
  intro i x y s
  rcases i with k | (_ | _) | a
  · simp only [dualF, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_add, Prod.smul_snd,
      Prod.snd_sub, mulVec_add, mulVec_smul, mulVec_sub, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, add_smul, smul_sub, sub_smul, smul_smul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · simp only [dualF, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    try ring
  · simp only [dualF, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    try ring
  · simp only [dualF, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    try ring

end SDDPAux


open Matrix

namespace SDDPAux
open ShapiroSDDP.Convergence

variable (I : Instance)

noncomputable def cutK (t : ℕ) (C : Finset (Cut I (t + 1)))
    (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) C) : Cut I t :=
  ((1 / (I.N (t + 1) : ℝ)) * ∑ j, ((d j).1 ⬝ᵥ I.b t j + ∑ a : C, (d j).2 a * (a : Cut I (t+1)).1),
    -((1 / (I.N (t + 1) : ℝ)) • ∑ j, (I.B t j)ᵀ *ᵥ (d j).1))

lemma cutAt_eq (t : ℕ) (x : Fin (I.n t) → ℝ) (C : Finset (Cut I (t + 1)))
    (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) C) : cutAt I t x C d = cutK I t C d := by
  have hg : (-((1 / (I.N (t + 1) : ℝ)) • ∑ j, (I.B t j)ᵀ *ᵥ (d j).1)) ⬝ᵥ x =
      -((1 / (I.N (t + 1) : ℝ)) * ∑ j, (d j).1 ⬝ᵥ (I.B t j *ᵥ x)) := by
    rw [neg_dotProduct, smul_dotProduct, sum_dotProduct]
    simp [mulVec_transpose, dotProduct_mulVec]
  simp only [cutAt, cutK]
  refine Prod.ext ?_ rfl
  simp only
  rw [hg]
  simp only [cutDualObj, rhs, dotProduct_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

lemma cutEval_cutAt (t : ℕ) (xb x : Fin (I.n t) → ℝ) (C : Finset (Cut I (t + 1)))
    (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) C) :
    cutEval (cutAt I t xb C d) x = (1 / (I.N (t + 1) : ℝ)) * ∑ j, cutDualObj (rhs I t x j) C (d j) := by
  rw [cutAt_eq I t xb, ← cutAt_eq I t x]
  simp only [cutAt, cutEval]
  ring

theorem finite_cuts' (t : ℕ) (D : Finset (Cut I (t + 1))) :
    ∃ F : Finset (Cut I t), ∀ (x : Fin (I.n t) → ℝ)
      (d : Fin (I.N (t + 1)) → CutDual (I.m (t + 1)) D),
      (∀ j, IsBasicOptDual (I.A t j) (rhs I t x j) D (I.c t j) (d j)) →
        cutAt I t x D d ∈ F := by
  classical
  have hfin : (Set.pi Set.univ (fun j : Fin (I.N (t + 1)) =>
      Set.extremePoints ℝ (CutDualFeas (I.A t j) D (I.c t j)))).Finite :=
    Set.Finite.pi (fun j => dual_extremePoints_finite _ _ _)
  refine ⟨(hfin.image (cutK I t D)).toFinset, fun x d hd => ?_⟩
  rw [Set.Finite.mem_toFinset, cutAt_eq]
  exact ⟨d, fun j _ => (hd j).1, rfl⟩

lemma finset_stab {α : Type*} (s : ℕ → Finset α) (U : Finset α) (hmono : ∀ k, s k ⊆ s (k + 1))
    (hU : ∀ k, s k ⊆ U) : ∃ K, ∀ k, K ≤ k → s k = s K := by
  classical
  let β := {D : Finset α // D ⊆ U}
  haveI : Finite β := Finite.of_injective
    (fun D : β => (⟨D.1, Finset.mem_powerset.2 D.2⟩ : U.powerset))
    (by intro a b h; exact Subtype.ext (congrArg (fun z : U.powerset => z.1) h))
  let a : ℕ →o β := ⟨fun k => ⟨s k, hU k⟩, monotone_nat_of_le_succ (fun k => hmono k)⟩
  obtain ⟨K, hK⟩ := WellFoundedGT.monotone_chain_condition a
  exact ⟨K, fun k hk => (congrArg Subtype.val (hK k hk)).symm⟩

section Runs

variable {I} {C₀ : (t : ℕ) → Finset (Cut I t)} {sol : Oracle I} {M : ℕ}
  {ω : ℕ → Fin M → Scen I} {cuts : ℕ → (t : ℕ) → Finset (Cut I t)}

lemma run_mono (hrun : IsRun I C₀ sol ω cuts) (k t : ℕ) : cuts k t ⊆ cuts (k + 1) t := by
  have := hrun.2 k t
  split_ifs at this with h
  · obtain ⟨d, -, heq⟩ := this
    rw [heq]; exact Finset.subset_union_left
  · rw [this]

lemma run_const (hrun : IsRun I C₀ sol ω cuts) (t : ℕ) (ht : ¬ (1 ≤ t ∧ t + 1 ≤ I.T)) (k : ℕ) :
    cuts k t = C₀ t := by
  induction k with
  | zero => rw [hrun.1]
  | succ k ih =>
    have := hrun.2 k t
    rw [if_neg ht] at this
    rw [this, ih]

end Runs

theorem cut_universe (C₀ : (t : ℕ) → Finset (Cut I t)) (sol : Oracle I) (M : ℕ) (t : ℕ) :
    ∃ U : Finset (Cut I t), ∀ (ω : ℕ → Fin M → Scen I) (cuts : ℕ → (t : ℕ) → Finset (Cut I t)),
      IsRun I C₀ sol ω cuts → ∀ k, cuts k t ⊆ U := by
  classical
  have key : ∀ r t, I.T - t ≤ r → ∃ U : Finset (Cut I t), ∀ (ω : ℕ → Fin M → Scen I)
      (cuts : ℕ → (t : ℕ) → Finset (Cut I t)), IsRun I C₀ sol ω cuts → ∀ k, cuts k t ⊆ U := by
    intro r
    induction r with
    | zero =>
      intro t ht
      exact ⟨C₀ t, fun ω cuts hrun k => by rw [run_const hrun t (by omega) k]⟩
    | succ r ih =>
      intro t ht
      by_cases h : I.T - t ≤ r
      · exact ih t h
      by_cases ht1 : 1 ≤ t
      · obtain ⟨U', hU'⟩ := ih (t + 1) (by omega)
        choose F hF using (fun D => finite_cuts' I t D)
        refine ⟨C₀ t ∪ U'.powerset.biUnion F, fun ω cuts hrun k => ?_⟩
        induction k with
        | zero => rw [hrun.1]; exact Finset.subset_union_left
        | succ k ihk =>
          have := hrun.2 k t
          rw [if_pos ⟨ht1, by omega⟩] at this
          obtain ⟨d, hd, heq⟩ := this
          rw [heq]
          refine Finset.union_subset ihk ?_
          intro a ha
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
          obtain ⟨i, rfl⟩ := ha
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨cuts (k + 1) (t + 1),
            Finset.mem_powerset.2 (hU' ω cuts hrun (k + 1)), hF _ _ _ (hd i)⟩)
      · exact ⟨C₀ t, fun ω cuts hrun k => by rw [run_const hrun t (by omega) k]⟩
  exact key (I.T - t) t le_rfl

theorem run_stab (C₀ : (t : ℕ) → Finset (Cut I t)) (sol : Oracle I) {M : ℕ}
    (ω : ℕ → Fin M → Scen I) (cuts : ℕ → (t : ℕ) → Finset (Cut I t))
    (hrun : IsRun I C₀ sol ω cuts) : ∃ K, ∀ k, K ≤ k → cuts k = cuts K := by
  have : ∀ t, ∃ K, ∀ k, K ≤ k → cuts k t = cuts K t := by
    intro t
    obtain ⟨U, hU⟩ := cut_universe I C₀ sol M t
    exact finset_stab (fun k => cuts k t) U (fun k => run_mono hrun k t) (hU ω cuts hrun)
  choose Kf hKf using this
  refine ⟨(Finset.range I.T).sup Kf, fun k hk => funext fun t => ?_⟩
  by_cases ht : t < I.T
  · have hle : Kf t ≤ (Finset.range I.T).sup Kf := Finset.le_sup (Finset.mem_range.2 ht)
    rw [hKf t k (le_trans hle hk), hKf t _ hle]
  · rw [run_const hrun t (by omega), run_const hrun t (by omega)]

end SDDPAux


open Matrix

namespace SDDPAux
open ShapiroSDDP.Convergence

variable {I : Instance}

lemma V_T (x : Fin (I.n I.T) → ℝ) : V I I.T x = 0 := by
  simp [V, Vrem]

lemma V_eq (t : ℕ) (ht : t + 1 ≤ I.T) (x : Fin (I.n t) → ℝ) :
    V I t x = (1 / (I.N (t + 1) : ℝ)) * ∑ j, Qo I t x j := by
  have h : I.T - t = (I.T - (t + 1)) + 1 := by omega
  unfold V
  rw [h]
  rfl

lemma reach_succ {t : ℕ} (ht : 1 ≤ t) {x : Fin (I.n t) → ℝ} (hx : x ∈ Reach I t)
    {j : Fin (I.N (t + 1))} {y : Fin (I.n (t + 1)) → ℝ} (hy : y ∈ Feas I t x j) :
    y ∈ Reach I (t + 1) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact ⟨x, hx, j, hy⟩

lemma Qo_le (hfin : FiniteValued I) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t + 1 ≤ I.T)
    {x : Fin (I.n t) → ℝ} (hx : x ∈ Reach I t) (j : Fin (I.N (t + 1)))
    {y : Fin (I.n (t + 1)) → ℝ} (hy : y ∈ Feas I t x j) :
    Qo I t x j ≤ I.c t j ⬝ᵥ y + V I (t + 1) y :=
  csInf_le (hfin t ht1 ht2 x hx j).2 ⟨y, hy, rfl⟩

lemma le_Qo (hfin : FiniteValued I) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t + 1 ≤ I.T)
    {x : Fin (I.n t) → ℝ} (hx : x ∈ Reach I t) (j : Fin (I.N (t + 1))) (L : ℝ)
    (hL : ∀ y ∈ Feas I t x j, L ≤ I.c t j ⬝ᵥ y + V I (t + 1) y) : L ≤ Qo I t x j := by
  apply le_csInf ((hfin t ht1 ht2 x hx j).1.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hL y hy

lemma lpfeas_of_valid {t : ℕ} {x : Fin (I.n t) → ℝ} {j : Fin (I.N (t + 1))}
    {y : Fin (I.n (t + 1)) → ℝ} (hy : y ∈ Feas I t x j) (hyR : y ∈ Reach I (t + 1))
    (D : Finset (Cut I (t + 1)))
    (hD : ∀ a ∈ D, ∀ z ∈ Reach I (t + 1), cutEval a z ≤ V I (t + 1) z) :
    (y, V I (t + 1) y) ∈ CutLPFeas (I.A t j) (rhs I t x j) D :=
  ⟨hy.1, hy.2, fun a ha => hD a ha y hyR⟩

/-- The value of a dual feasible point bounds `Q̃_{t+1,j}(x)` from below, when the cuts are valid. -/
lemma dual_le_Qo (hfin : FiniteValued I) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t + 1 ≤ I.T)
    {x : Fin (I.n t) → ℝ} (hx : x ∈ Reach I t) (j : Fin (I.N (t + 1)))
    (D : Finset (Cut I (t + 1)))
    (hD : ∀ a ∈ D, ∀ z ∈ Reach I (t + 1), cutEval a z ≤ V I (t + 1) z)
    (d : CutDual (I.m (t + 1)) D) (hd : d ∈ CutDualFeas (I.A t j) D (I.c t j)) :
    cutDualObj (rhs I t x j) D d ≤ Qo I t x j := by
  apply le_Qo hfin ht1 ht2 hx j
  intro y hy
  exact weak_duality _ _ _ _ d hd _ (lpfeas_of_valid hy (reach_succ ht1 hx hy) D hD)

theorem valid_all (hfin : FiniteValued I) {C₀ : (t : ℕ) → Finset (Cut I t)}
    (hC₀ : ValidInit I C₀) {sol : Oracle I} {M : ℕ} {ω : ℕ → Fin M → Scen I}
    {cuts : ℕ → (t : ℕ) → Finset (Cut I t)} (hrun : IsRun I C₀ sol ω cuts) :
    ∀ k t, 1 ≤ t → t ≤ I.T → ∀ a ∈ cuts k t, ∀ x ∈ Reach I t, cutEval a x ≤ V I t x := by
  have hT : ∀ k, ∀ a ∈ cuts k I.T, ∀ x ∈ Reach I I.T, cutEval a x ≤ V I I.T x := by
    intro k a ha x _
    rw [run_const hrun I.T (by omega) k, hC₀.1, Finset.mem_singleton] at ha
    subst ha
    simp [cutEval, V_T]
  intro k
  induction k with
  | zero =>
    intro t ht1 ht2 a ha x hx
    rcases (show t = I.T ∨ t + 1 ≤ I.T by omega) with h | h
    · subst h; exact hT 0 a ha x hx
    · rw [hrun.1] at ha
      exact (hC₀.2 t ht1 h).2 a ha x hx
  | succ k ih =>
    have key : ∀ r t, 1 ≤ t → t ≤ I.T → I.T - t ≤ r →
        ∀ a ∈ cuts (k + 1) t, ∀ x ∈ Reach I t, cutEval a x ≤ V I t x := by
      intro r
      induction r with
      | zero =>
        intro t ht1 ht2 hr
        obtain rfl : t = I.T := by omega
        exact hT (k + 1)
      | succ r ihr =>
        intro t ht1 ht2 hr
        rcases (show t = I.T ∨ t + 1 ≤ I.T by omega) with h | h
        · subst h; exact hT (k + 1)
        have hnext := ihr (t + 1) (by omega) h (by omega)
        have := hrun.2 k t
        rw [if_pos ⟨ht1, h⟩] at this
        obtain ⟨d, hd, heq⟩ := this
        intro a ha x hx
        rw [heq, Finset.mem_union] at ha
        rcases ha with ha | ha
        · exact ih t ht1 ht2 a ha x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
        obtain ⟨i, rfl⟩ := ha
        rw [cutEval_cutAt, V_eq t h]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j _
        exact dual_le_Qo hfin ht1 h hx j _ hnext _ (hd i j).1.1
    intro t ht1 ht2
    exact key (I.T - t) t ht1 ht2 le_rfl

theorem cut_valid' (I : Instance) (hfin : FiniteValued I) (C₀ : (t : ℕ) → Finset (Cut I t))
    (hC₀ : ValidInit I C₀) (sol : Oracle I) {M : ℕ} (ω : ℕ → Fin M → Scen I)
    (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) (hrun : IsRun I C₀ sol ω cuts) :
    (∀ k t, 1 ≤ t → t + 1 ≤ I.T → ∀ a ∈ cuts k t, ∀ x ∈ Reach I t, cutEval a x ≤ V I t x) ∧
      ∀ k t, 1 ≤ t → t + 1 ≤ I.T → ∀ x ∈ Reach I t, ∀ j : Fin (I.N (t + 1)),
        ∀ y ∈ Feas I t x j,
          (y, V I (t + 1) y) ∈ CutLPFeas (I.A t j) (rhs I t x j) (cuts k (t + 1)) := by
  refine ⟨fun k t h1 h2 => valid_all hfin hC₀ hrun k t h1 (by omega), ?_⟩
  intro k t h1 h2 x hx j y hy
  exact lpfeas_of_valid hy (reach_succ h1 hx hy) _
    (valid_all hfin hC₀ hrun k (t + 1) (by omega) h2)

/-! ### The forward policy -/

lemma fwd_succ (sol : Oracle I) (C : (t : ℕ) → Finset (Cut I t)) (u : ℕ) (hu : u < I.T - 1)
    (s : Scen I) :
    fwd I sol C (u + 2) s = sol.next (u + 1) (C (u + 2)) (fwd I sol C (u + 1) s) (s ⟨u, hu⟩) := by
  simp only [fwd, dif_pos hu]

theorem fwd_impl (sol : Oracle I) (C : (t : ℕ) → Finset (Cut I t)) :
    ∀ (t : ℕ) (s s' : Scen I), (∀ u : Fin (I.T - 1), (u : ℕ) + 2 ≤ t → s u = s' u) →
      fwd I sol C t s = fwd I sol C t s'
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | t + 2, s, s', h => by
    simp only [fwd]
    split_ifs with ht
    · rw [fwd_impl sol C (t + 1) s s' (fun u hu => h u (by omega)), h ⟨t, ht⟩ (le_refl _)]
    · rfl

/-- (A1) at a single iteration with cut sets `C`. -/
def A1at (sol : Oracle I) (C : (t : ℕ) → Finset (Cut I t)) : Prop :=
  CutLPFinite I.A₁ I.b₁ (C 1) I.c₁ ∧
    ∀ (s : Scen I) (u : Fin (I.T - 1)),
      CutLPFinite (I.A ((u : ℕ) + 1) (s u))
        (rhs I ((u : ℕ) + 1) (fwd I sol C ((u : ℕ) + 1) s) (s u))
        (C ((u : ℕ) + 2)) (I.c ((u : ℕ) + 1) (s u))

lemma first_opt {sol : Oracle I} (hsol : OracleSpec I sol) {C : (t : ℕ) → Finset (Cut I t)}
    (hA : A1at sol C) : ∃ θ, IsCutLPOpt I.A₁ I.b₁ (C 1) I.c₁ (sol.first (C 1), θ) :=
  hsol.1 (C 1) (attainment' _ _ _ _ hA.1)

lemma next_opt {sol : Oracle I} (hsol : OracleSpec I sol) {C : (t : ℕ) → Finset (Cut I t)}
    (hA : A1at sol C) (s : Scen I) (u : Fin (I.T - 1)) :
    ∃ θ, IsCutLPOpt (I.A ((u : ℕ) + 1) (s u))
        (rhs I ((u : ℕ) + 1) (fwd I sol C ((u : ℕ) + 1) s) (s u))
        (C ((u : ℕ) + 2)) (I.c ((u : ℕ) + 1) (s u)) (fwd I sol C ((u : ℕ) + 2) s, θ) := by
  rw [fwd_succ sol C u u.isLt]
  exact hsol.2 ((u : ℕ) + 1) (by omega) (by have := u.isLt; omega) _ _ _
    (attainment' _ _ _ _ (hA.2 s u))

lemma fwd_feas {sol : Oracle I} (hsol : OracleSpec I sol) {C : (t : ℕ) → Finset (Cut I t)}
    (hA : A1at sol C) (s : Scen I) (u : Fin (I.T - 1)) :
    fwd I sol C ((u : ℕ) + 2) s ∈ Feas I ((u : ℕ) + 1) (fwd I sol C ((u : ℕ) + 1) s) (s u) := by
  obtain ⟨θ, hθ, -⟩ := next_opt hsol hA s u
  exact ⟨hθ.1, hθ.2.1⟩

lemma fwd_feas1 {sol : Oracle I} (hsol : OracleSpec I sol) {C : (t : ℕ) → Finset (Cut I t)}
    (hA : A1at sol C) (s : Scen I) : fwd I sol C 1 s ∈ Feas₁ I := by
  obtain ⟨θ, hθ, -⟩ := first_opt hsol hA
  exact ⟨hθ.1, hθ.2.1⟩

lemma fwd_reach {sol : Oracle I} (hsol : OracleSpec I sol) {C : (t : ℕ) → Finset (Cut I t)}
    (hA : A1at sol C) (s : Scen I) :
    ∀ t, 1 ≤ t → t ≤ I.T → fwd I sol C t s ∈ Reach I t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; exact fwd_feas1 hsol hA s
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      have hu : u < I.T - 1 := by omega
      exact reach_succ (by omega) (ih (by omega) (by omega)) (fwd_feas hsol hA s ⟨u, hu⟩)

end SDDPAux


open ShapiroSDDP.Convergence

theorem solution (I : Instance) (hfin : FiniteValued I) (C₀ : (t : ℕ) → Finset (Cut I t))
    (hC₀ : ValidInit I C₀) (sol : Oracle I) {M : ℕ} (ω : ℕ → Fin M → Scen I)
    (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) (hrun : IsRun I C₀ sol ω cuts) (k : ℕ)
    (hk : CutLPFinite I.A₁ I.b₁ (cuts k 1) I.c₁) :
    cutLPVal I.A₁ I.b₁ (cuts k 1) I.c₁ ≤ optVal I := by
  obtain ⟨⟨p, hp⟩, hbdd⟩ := hk
  have hT := I.hT
  have hval := SDDPAux.valid_all hfin hC₀ hrun k 1 le_rfl (by omega)
  unfold cutLPVal optVal
  apply le_csInf
  · exact ⟨_, ⟨p.1, ⟨hp.1, hp.2.1⟩, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact csInf_le hbdd ⟨(x, V I 1 x), ⟨hx.1, hx.2, fun a ha => hval a ha x hx⟩, rfl⟩
