-- Prove2me | solution 1 for ShapiroSDDP.Convergence.attainment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:49:00.02569+00:00
-- url     : https://prove2.me/submissions/57362a54-f72c-425f-afd1-04d69040871b

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


open ShapiroSDDP.Convergence

theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (C : Finset (ℝ × (Fin n → ℝ))) (c : Fin n → ℝ) (hfin : CutLPFinite A h C c) :
    ∃ p, IsCutLPOpt A h C c p :=
  SDDPAux.attainment' A h C c hfin
