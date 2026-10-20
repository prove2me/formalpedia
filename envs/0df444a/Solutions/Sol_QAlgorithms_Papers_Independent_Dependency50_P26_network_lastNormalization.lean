-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.network_lastNormalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:49:22.512434+00:00
-- url     : https://prove2.me/submissions/81dee5e7-2221-47fc-9d78-6d0dff57182f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

lemma g52a_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma g52a_traceLeft_psd {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) : (traceLeft M).PosSemidef := by
  have : traceLeft M = ∑ a, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'; simp [traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

lemma g52a_retained_psd {s : Signature} (net : MemoryNetwork s) :
    ∀ n, (net.retained n).PosSemidef := by
  intro n
  induction n with
  | zero =>
    let v : Fin (net.memory 0) × Basis s 0 → ℂ := fun a => if a.1.val = 0 then 1 else 0
    have : net.retained 0 = Matrix.vecMulVec v (star v) := by
      ext a b
      simp only [MemoryNetwork.retained, Matrix.vecMulVec_apply, Pi.star_apply, v]
      split_ifs <;> simp_all
    rw [this]
    exact Matrix.posSemidef_vecMulVec_self_star v
  | succ n ih =>
    let Kb : Fin (net.krausCount n) →
        Matrix (Fin (net.memory (n+1)) × Basis s (n+1)) (Fin (net.memory n) × Basis s n) ℂ :=
      fun e => Matrix.of fun a c =>
        if a.2.2.2 = c.2 then net.kraus n e (a.2.1, a.1) (a.2.2.1, c.1) else 0
    have hK1 : ∀ e a (M : Matrix (Fin (net.memory n) × Basis s n)
        (Fin (net.memory n) × Basis s n) ℂ) q, (Kb e * M) a q =
        ∑ u, net.kraus n e (a.2.1, a.1) (a.2.2.1, u) * M (u, a.2.2.2) q := by
      intro e a M q
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_eq_single a.2.2.2]
      · simp [Kb]
      · intro c _ hc; simp [Kb, Ne.symm hc]
      · simp
    have hK2 : ∀ e (Y : Matrix (Fin (net.memory (n+1)) × Basis s (n+1))
        (Fin (net.memory n) × Basis s n) ℂ) a b, (Y * (Kb e)ᴴ) a b =
        ∑ v, Y a (v, b.2.2.2) * star (net.kraus n e (b.2.1, b.1) (b.2.2.1, v)) := by
      intro e Y a b
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_eq_single b.2.2.2]
      · simp [Kb, Matrix.conjTranspose_apply]
      · intro c _ hc; simp [Kb, Matrix.conjTranspose_apply, Ne.symm hc]
      · simp
    have : net.retained (n+1) = ∑ e, Kb e * net.retained n * (Kb e)ᴴ := by
      ext a b
      rw [Matrix.sum_apply]
      show (∑ e, ∑ u, ∑ v, net.kraus n e (a.2.1, a.1) (a.2.2.1, u) *
        net.retained n (u, a.2.2.2) (v, b.2.2.2) *
        conj (net.kraus n e (b.2.1, b.1) (b.2.2.1, v))) = _
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hK2]
      simp only [hK1, Finset.sum_mul]
      rw [Finset.sum_comm]
      rfl
    rw [this]
    exact Matrix.posSemidef_sum _ fun e _ => ih.mul_mul_conjTranspose_same _

/-- PDF p.6, Lemma 4: the prefix is the network actually constructed from earlier vertices. -/
theorem solution (s : Signature) (net : MemoryNetwork s) (n : ℕ) :
    (net.choi (n+1)).PosSemidef ∧
      traceLeft (net.choi (n+1)) =
        Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) (net.choi n) := by
  refine ⟨g52a_traceLeft_psd _ (g52a_retained_psd net (n+1)), ?_⟩
  have key : ∀ (i i' : Fin (s.input n)) (u v : Fin (net.memory n)),
      ∑ o, ∑ m, ∑ e, net.kraus n e (o, m) (i, u) * conj (net.kraus n e (o, m) (i', v)) =
        if i' = i ∧ v = u then 1 else 0 := by
    intro i i' u v
    have h := congrFun (congrFun (net.trace_preserving n) (i', v)) (i, u)
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq, RCLike.star_def] at h
    rw [← g52a_sum3]
    refine h ▸ ?_
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun o _ =>
      Finset.sum_congr rfl fun m _ => mul_comm _ _
  ext ⟨i, x⟩ ⟨i', x'⟩
  change (∑ o, ∑ m, ∑ e, ∑ u, ∑ v, net.kraus n e (o, m) (i, u) *
      net.retained n (u, x) (v, x') * conj (net.kraus n e (o, m) (i', v))) =
    (Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) (net.choi n)) (i, x) (i', x')
  rw [Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun m _ =>
    g52a_sum3 (fun e u v => net.kraus n e (o, m) (i, u) *
      net.retained n (u, x) (v, x') * conj (net.kraus n e (o, m) (i', v)))]
  rw [Finset.sum_congr rfl fun o _ =>
    g52a_sum3 (fun m u v => ∑ e, net.kraus n e (o, m) (i, u) *
      net.retained n (u, x) (v, x') * conj (net.kraus n e (o, m) (i', v)))]
  rw [g52a_sum3 (fun o u v => ∑ m, ∑ e, net.kraus n e (o, m) (i, u) *
      net.retained n (u, x) (v, x') * conj (net.kraus n e (o, m) (i', v)))]
  have hterm : ∀ u v, (∑ o, ∑ m, ∑ e, net.kraus n e (o, m) (i, u) *
      net.retained n (u, x) (v, x') * conj (net.kraus n e (o, m) (i', v))) =
      net.retained n (u, x) (v, x') * (if i' = i ∧ v = u then 1 else 0) := by
    intro u v
    rw [← key, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [hterm]
  simp only [MemoryNetwork.choi, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    traceLeft, Matrix.of_apply]
  by_cases hi : i = i'
  · subst hi
    simp [Finset.sum_ite_eq']
  · have : ¬ i' = i := Ne.symm hi
    simp [hi, this]


end

