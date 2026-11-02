-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:08:07.163232+00:00
-- url     : https://prove2.me/submissions/fac47f88-0d7a-4914-ad50-601a97977d65

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm
import Theorems.Thm_RankOneBimatrix_BinSearch_br_extreme_exists
import Theorems.Thm_RankOneBimatrix_BinSearch_dual_extreme_exists
import Theorems.Thm_RankOneBimatrix_BinSearch_extreme_lambda_size
import Theorems.Thm_RankOneBimatrix_BinSearch_lemma_9
import Theorems.Thm_RankOneBimatrix_BinSearch_pmax_pmin_extreme_exists
import Theorems.Thm_RankOneBimatrix_BinSearch_primal_extreme_exists
import Theorems.Thm_RankOneBimatrix_BinSearch_strong_duality

open Matrix RankOneBimatrix.BinSearch

namespace R1BSAux

variable {m n : ℕ}

lemma gap_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (mu : ℝ) (p : PPoint m n)
    (hp : p ∈ PFeas A b mu) (q : DPoint n) (hq : q.1 ∈ Mixed n) :
    p.2.1 - DValue b mu q =
      ∑ j, p.2.2 j * q.1 j + ∑ i, p.1 i * (-((A *ᵥ q.1) i + q.2)) := by
  obtain ⟨⟨_, hx1⟩, _, heq⟩ := hp
  obtain ⟨_, hy1⟩ := hq
  have hs' : ∀ j, p.2.2 j = (A.transpose *ᵥ p.1) j + p.2.1 - b j * mu := fun j => by
    linarith [heq j]
  have h1 : ∑ j, (A.transpose *ᵥ p.1) j * q.1 j = ∑ i, p.1 i * (A *ᵥ q.1) i := by
    simp only [mulVec, dotProduct, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e1 : ∑ j, p.2.2 j * q.1 j =
      ∑ j, (A.transpose *ᵥ p.1) j * q.1 j + p.2.1 * ∑ j, q.1 j - mu * ∑ j, b j * q.1 j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs' j]; ring
  have e2 : ∑ i, p.1 i * (-((A *ᵥ q.1) i + q.2)) =
      -(∑ i, p.1 i * (A *ᵥ q.1) i) - q.2 * ∑ i, p.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, e2, h1, hx1, hy1]
  simp only [DValue, dotProduct]
  ring

lemma gap_terms_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (mu : ℝ)
    (p : PPoint m n) (hp : p ∈ PFeas A b mu) (q : DPoint n) (hq : q ∈ DSet A) :
    (∀ j, 0 ≤ p.2.2 j * q.1 j) ∧ (∀ i, 0 ≤ p.1 i * (-((A *ᵥ q.1) i + q.2))) := by
  obtain ⟨⟨hx0, _⟩, hs0, _⟩ := hp
  obtain ⟨⟨hy0, _⟩, hD⟩ := hq
  exact ⟨fun j => mul_nonneg (hs0 j) (hy0 j),
    fun i => mul_nonneg (hx0 i) (by linarith [hD i])⟩

lemma weak_duality (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (mu : ℝ)
    (p : PPoint m n) (hp : p ∈ PFeas A b mu) (q : DPoint n) (hq : q ∈ DSet A) :
    DValue b mu q ≤ p.2.1 := by
  have hg := gap_eq A b mu p hp q hq.1
  obtain ⟨h1, h2⟩ := gap_terms_nonneg A b mu p hp q hq
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => h1 j)
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => h2 i)
  linarith

lemma compl_of_eq (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (mu : ℝ)
    (p : PPoint m n) (hp : p ∈ PFeas A b mu) (q : DPoint n) (hq : q ∈ DSet A)
    (hv : p.2.1 = DValue b mu q) :
    (∀ i, (A *ᵥ q.1) i + q.2 < 0 → p.1 i = 0) ∧ (∀ j, 0 < q.1 j → p.2.2 j = 0) := by
  have hg := gap_eq A b mu p hp q hq.1
  obtain ⟨h1, h2⟩ := gap_terms_nonneg A b mu p hp q hq
  have s1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => h1 j)
  have s2 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => h2 i)
  have z1 : ∑ j, p.2.2 j * q.1 j = 0 := by linarith
  have z2 : ∑ i, p.1 i * (-((A *ᵥ q.1) i + q.2)) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h1 j)] at z1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h2 i)] at z2
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have := z2 i (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; linarith
  · have := z1 j (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; linarith

lemma eq_of_compl (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (mu : ℝ)
    (p : PPoint m n) (hp : p ∈ PFeas A b mu) (q : DPoint n) (hq : q ∈ DSet A)
    (hM : ∀ i, (A *ᵥ q.1) i + q.2 < 0 → p.1 i = 0) (hN : ∀ j, 0 < q.1 j → p.2.2 j = 0) :
    p.2.1 = DValue b mu q := by
  have hg := gap_eq A b mu p hp q hq.1
  have z1 : ∑ j, p.2.2 j * q.1 j = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_eq_of_le (hq.1.1 j) with h | h
    · rw [hN j h]; ring
    · rw [← h]; ring
  have z2 : ∑ i, p.1 i * (-((A *ᵥ q.1) i + q.2)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases lt_or_eq_of_le (hq.2 i) with h | h
    · rw [hM i h]; ring
    · rw [h]; ring
  linarith

lemma mem_Mset (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ) (i : Fin m) :
    i ∈ Mset A b l ↔ ∃ p ∈ Yopt A b l, (A *ᵥ p.1) i + p.2 < 0 := by
  unfold Mset; simp

lemma mem_Nset (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ) (j : Fin n) :
    j ∈ Nset A b l ↔ ∃ p ∈ Yopt A b l, 0 < p.1 j := by
  unfold Nset; simp

/-- Every point of the face `P(M(l),N(l))` has primal value equal to the dual value of
every dual optimum at `l`, evaluated at its own parameter. -/
lemma face_value (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ)
    (w : PolyPoint m n) (hw : w ∈ PFace A b (Mset A b l) (Nset A b l))
    (q : DPoint n) (hq : q ∈ Yopt A b l) :
    w.2.2.1 = DValue b w.1 q := by
  obtain ⟨hP, hxM, hsN⟩ := hw
  exact eq_of_compl A b w.1 w.2 hP q hq.1
    (fun i hi => hxM i ((mem_Mset A b l i).2 ⟨q, hq, hi⟩))
    (fun j hj => hsN j ((mem_Nset A b l j).2 ⟨q, hq, hj⟩))

lemma face_opt (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ)
    (hY : (Yopt A b l).Nonempty)
    (w : PolyPoint m n) (hw : w ∈ PFace A b (Mset A b l) (Nset A b l)) :
    w.2 ∈ POpt A b w.1 := by
  obtain ⟨q, hq⟩ := hY
  have hv := face_value A b l w hw q hq
  refine ⟨hw.1, ⟨w.2, hw.1, rfl⟩, ?_⟩
  rintro _ ⟨p', hp', rfl⟩
  rw [hv]
  exact weak_duality A b w.1 p' hp' q hq.1

lemma face_contains (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ)
    (hY : (Yopt A b l).Nonempty)
    (w : PolyPoint m n) (hw : w ∈ PFace A b (Mset A b l) (Nset A b l))
    (p' : PPoint m n) (hp' : p' ∈ POpt A b w.1) :
    ((w.1, p') : PolyPoint m n) ∈ PFace A b (Mset A b l) (Nset A b l) := by
  have hwopt := face_opt A b l hY w hw
  have hvv : p'.2.1 = w.2.2.1 := IsLeast.unique hp'.2 hwopt.2
  refine ⟨hp'.1, fun i hi => ?_, fun j hj => ?_⟩
  · obtain ⟨q, hq, hlt⟩ := (mem_Mset A b l i).1 hi
    have := face_value A b l w hw q hq
    exact (compl_of_eq A b w.1 p' hp'.1 q hq.1 (by rw [hvv, this])).1 i hlt
  · obtain ⟨q, hq, hlt⟩ := (mem_Nset A b l j).1 hj
    have := face_value A b l w hw q hq
    exact (compl_of_eq A b w.1 p' hp'.1 q hq.1 (by rw [hvv, this])).2 j hlt

lemma own_face (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (l : ℝ)
    (hSD : ∃ p ∈ POpt A b l, ∃ q ∈ Yopt A b l, p.2.1 = DValue b l q)
    (p : PPoint m n) (hp : p ∈ POpt A b l) :
    ((l, p) : PolyPoint m n) ∈ PFace A b (Mset A b l) (Nset A b l) := by
  obtain ⟨p0, hp0, q0, hq0, hv0⟩ := hSD
  have hpp : p.2.1 = p0.2.1 := IsLeast.unique hp.2 hp0.2
  have key : ∀ q ∈ Yopt A b l, p.2.1 = DValue b l q := by
    intro q hq
    have : DValue b l q = DValue b l q0 := IsGreatest.unique hq.2 hq0.2
    rw [hpp, hv0, this]
  refine ⟨hp.1, fun i hi => ?_, fun j hj => ?_⟩
  · obtain ⟨q, hq, hlt⟩ := (mem_Mset A b l i).1 hi
    exact (compl_of_eq A b l p hp.1 q hq.1 (key q hq)).1 i hlt
  · obtain ⟨q, hq, hlt⟩ := (mem_Nset A b l j).1 hj
    exact (compl_of_eq A b l p hp.1 q hq.1 (key q hq)).2 j hlt

lemma face_convex (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (M : Finset (Fin m)) (N : Finset (Fin n)) : Convex ℝ (PFace A b M N) := by
  intro w1 h1 w2 h2 t1 t2 ht1 ht2 hsum
  obtain ⟨⟨hx1, hs1, he1⟩, hM1, hN1⟩ := h1
  obtain ⟨⟨hx2, hs2, he2⟩, hM2, hN2⟩ := h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact convex_stdSimplex ℝ (Fin m) hx1 hx2 ht1 ht2 hsum
  · intro j
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hs1 j, hs2 j]
  · intro j
    simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul]
    linear_combination t1 * he1 j + t2 * he2 j
  · intro i hi
    simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hM1 i hi, hM2 i hi]
    ring
  · intro j hj
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hN1 j hj, hN2 j hj]
    ring

lemma combo (e0 ew : ℝ) (h0 : 0 ≤ e0) (hw : ew ≤ 0) :
    ∃ t1 t2 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ t1 + t2 = 1 ∧ t1 * e0 + t2 * ew = 0 := by
  rcases eq_or_lt_of_le h0 with h | h
  · exact ⟨1, 0, by norm_num, le_refl _, by norm_num, by rw [← h]; ring⟩
  · have hd : 0 < e0 - ew := by linarith
    refine ⟨-ew / (e0 - ew), e0 / (e0 - ew), div_nonneg (by linarith) hd.le,
      div_nonneg h0 hd.le, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring

lemma combo_fst (w0 w : PolyPoint m n) (t1 t2 : ℝ) :
    (t1 • w0 + t2 • w).1 = t1 * w0.1 + t2 * w.1 := by
  simp [Prod.fst_add, Prod.smul_fst]

lemma combo_dot (w0 w : PolyPoint m n) (t1 t2 : ℝ) (a : Fin m → ℝ) :
    (t1 • w0 + t2 • w).2.1 ⬝ᵥ a = t1 * (w0.2.1 ⬝ᵥ a) + t2 * (w.2.1 ⬝ᵥ a) := by
  simp [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, add_dotProduct,
    smul_dotProduct]

end R1BSAux

open Matrix RankOneBimatrix.BinSearch

namespace R1BSAux

variable {m n : ℕ}

def Inv (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ) (lo hi : ℝ) : Prop :=
  lo ≤ hi ∧ (∃ p ∈ POpt A b lo, lo ≤ p.1 ⬝ᵥ a) ∧ (∃ p ∈ POpt A b hi, p.1 ⬝ᵥ a ≤ hi)

def GenuineAt (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (lam : ℝ) : Prop :=
  O.primal lam ∈ PExtreme A b lam ∧
  (if lam ≤ (O.primal lam).1 ⬝ᵥ a then
    O.pmax (Mset A b lam) (Nset A b lam) lam ∈
        PmaxExtreme A a b (Mset A b lam) (Nset A b lam) lam ∧
      ((O.pmax (Mset A b lam) (Nset A b lam) lam).1 <
          (O.pmax (Mset A b lam) (Nset A b lam) lam).2.1 ⬝ᵥ a →
        O.brmax (Mset A b lam) (Nset A b lam) ∈ BRmaxExtreme A b (Mset A b lam) (Nset A b lam))
  else
    O.pmin (Mset A b lam) (Nset A b lam) lam ∈
        PminExtreme A a b (Mset A b lam) (Nset A b lam) lam ∧
      ((O.pmin (Mset A b lam) (Nset A b lam) lam).2.1 ⬝ᵥ a <
          (O.pmin (Mset A b lam) (Nset A b lam) lam).1 →
        O.brmin (Mset A b lam) (Nset A b lam) ∈ BRminExtreme A b (Mset A b lam) (Nset A b lam)))

lemma callsGenuine_eq (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (k : ℕ) :
    callsGenuine A a b O k = GenuineAt A a b O (midpoint A a b O k) := rfl

/-- The outcome of one iteration of Figure 2 from a state satisfying the invariant. -/
def StepOK (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (s : RunState m n) : Prop :=
  GenuineAt A a b O ((s.lo + s.hi) / 2) ∧
  (((step A a b O s).sol.2.1 ⬝ᵥ a = (step A a b O s).sol.1 ∧
      ((step A a b O s).sol ∈ Set.extremePoints ℝ (PmaxFeas A a b
          (Mset A b ((s.lo + s.hi) / 2)) (Nset A b ((s.lo + s.hi) / 2)) ((s.lo + s.hi) / 2)) ∨
        (step A a b O s).sol ∈ Set.extremePoints ℝ (PminFeas A a b
          (Mset A b ((s.lo + s.hi) / 2)) (Nset A b ((s.lo + s.hi) / 2)) ((s.lo + s.hi) / 2))) ∧
      (step A a b O s).sol.2 ∈ POpt A b (step A a b O s).sol.1) ∨
   (¬ ((step A a b O s).sol.2.1 ⬝ᵥ a = (step A a b O s).sol.1) ∧ s.lo < s.hi ∧
      Inv A a b (step A a b O s).lo (step A a b O s).hi ∧
      (step A a b O s).hi - (step A a b O s).lo ≤ (s.hi - s.lo) / 2 ∧
      (∃ M N, (step A a b O s).sol ∈ Set.extremePoints ℝ (PFace A b M N)) ∧
      ((step A a b O s).lo = s.lo ∨ (step A a b O s).lo = (step A a b O s).sol.1) ∧
      ((step A a b O s).hi = s.hi ∨ (step A a b O s).hi = (step A a b O s).sol.1)))

theorem step_spec (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (hadm : Admissible A a b O)
    (hP : ∀ l, (PExtreme A b l).Nonempty)
    (hD : ∀ l, (DExtreme A b l).Nonempty)
    (hSD : ∀ l, ∃ p ∈ POpt A b l, ∃ q ∈ Yopt A b l, p.2.1 = DValue b l q)
    (hPM : ∀ M N l, ((PmaxFeas A a b M N l).Nonempty → (PmaxExtreme A a b M N l).Nonempty) ∧
      ((PminFeas A a b M N l).Nonempty → (PminExtreme A a b M N l).Nonempty))
    (hBR : ∀ M N, ((PFace A b M N).Nonempty →
        BddAbove ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
        (BRmaxExtreme A b M N).Nonempty) ∧
      ((PFace A b M N).Nonempty →
        BddBelow ((fun q : PolyPoint m n => q.1) '' PFace A b M N) →
        (BRminExtreme A b M N).Nonempty))
    (s : RunState m n) (hinv : Inv A a b s.lo s.hi) :
    StepOK A a b O s := by
  obtain ⟨hle, ⟨pL, hpL, hpLa⟩, ⟨pH, hpH, hpHa⟩⟩ := hinv
  unfold StepOK GenuineAt
  set lam := (s.lo + s.hi) / 2 with hlam
  set p := O.primal lam with hpdef
  set M := Mset A b lam with hM
  set N := Nset A b lam with hN
  set z := O.pmax M N lam with hz
  set z' := (if z.1 < z.2.1 ⬝ᵥ a then O.brmax M N else z) with hz'
  set w := O.pmin M N lam with hw
  set w' := (if w.2.1 ⬝ᵥ a < w.1 then O.brmin M N else w) with hw'
  have hS : step A a b O s =
      if lam ≤ p.1 ⬝ᵥ a then ⟨z'.1, s.hi, z'⟩ else ⟨s.lo, w'.1, w'⟩ := by
    simp only [step]
    rfl
  have hp : p ∈ PExtreme A b lam := hadm.1 lam (hP lam)
  have hpO : p ∈ POpt A b lam := hp.1
  have hY : (Yopt A b lam).Nonempty := by
    obtain ⟨q, hq⟩ := hD lam
    exact ⟨q, hq.1⟩
  have hconv := face_convex A b M N
  have hw0 : ((lam, p) : PolyPoint m n) ∈ PFace A b M N := own_face A b lam (hSD lam) p hpO
  have hlo_lam : s.lo ≤ lam := by rw [hlam]; linarith
  have hlam_hi : lam ≤ s.hi := by rw [hlam]; linarith
  by_cases hA : lam ≤ p.1 ⬝ᵥ a
  · -- Case A: Pmax
    have hfe : (PmaxFeas A a b M N lam).Nonempty := ⟨(lam, p), hw0, hA, le_refl _⟩
    have hzE : z ∈ PmaxExtreme A a b M N lam := hadm.2.2.1 M N lam ((hPM M N lam).1 hfe)
    obtain ⟨⟨⟨hzF, hz1, hz2⟩, hzgr⟩, hzext⟩ := hzE
    rw [hS, if_pos hA, if_pos hA]
    by_cases hB : z.1 < z.2.1 ⬝ᵥ a
    · have hC : ∀ u ∈ PFace A b M N, lam ≤ u.1 → u.1 < u.2.1 ⬝ᵥ a := by
        intro u hu hl
        by_contra hcon
        push Not at hcon
        obtain ⟨t1, t2, ht1, ht2, hts, hte⟩ :=
          combo (p.1 ⬝ᵥ a - lam) (u.2.1 ⬝ᵥ a - u.1) (by linarith) (by linarith)
        have hv := hconv hw0 hu ht1 ht2 hts
        have hv1 := combo_fst ((lam, p) : PolyPoint m n) u t1 t2
        have hv2 := combo_dot ((lam, p) : PolyPoint m n) u t1 t2 a
        simp only at hv1 hv2
        have hfeas : t1 • ((lam, p) : PolyPoint m n) + t2 • u ∈ PmaxFeas A a b M N lam := by
          refine ⟨hv, ?_, ?_⟩
          · rw [hv1, hv2]; linear_combination (-1 : ℝ) * hte
          · rw [hv1]
            have e : t1 * lam + t2 * lam = lam := by linear_combination lam * hts
            have := mul_nonneg ht2 (sub_nonneg.2 hl)
            nlinarith
        have := hzgr.2 ⟨_, hfeas, rfl⟩
        simp only at this
        rw [hv1, hv2] at this
        have h0 : t1 * lam + t2 * u.1 - (t1 * (p.1 ⬝ᵥ a) + t2 * (u.2.1 ⬝ᵥ a)) = 0 := by
          linear_combination (-1 : ℝ) * hte
        linarith
      have hBnd : ∀ u ∈ PFace A b M N, u.1 < s.hi := by
        intro u hu
        by_contra hcon
        push Not at hcon
        obtain ⟨t1, t2, ht1, ht2, hts, hte⟩ :=
          combo (u.1 - s.hi) (lam - s.hi) (by linarith) (by linarith)
        have hv := hconv hu hw0 ht1 ht2 hts
        have hv1 := combo_fst u ((lam, p) : PolyPoint m n) t1 t2
        simp only at hv1
        have hvhi : (t1 • u + t2 • ((lam, p) : PolyPoint m n)).1 = s.hi := by
          rw [hv1]; linear_combination hte + s.hi * hts
        have hpH' : pH ∈ POpt A b (t1 • u + t2 • ((lam, p) : PolyPoint m n)).1 := by
          rw [hvhi]; exact hpH
        have hc := face_contains A b lam hY _ hv pH hpH'
        have := hC _ hc (by simp only; rw [hvhi]; exact hlam_hi)
        simp only at this
        rw [hvhi] at this
        linarith
      have hbdd : BddAbove ((fun q : PolyPoint m n => q.1) '' PFace A b M N) := by
        refine ⟨s.hi, ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        exact (hBnd u hu).le
      have hbr : O.brmax M N ∈ BRmaxExtreme A b M N :=
        hadm.2.2.2.2.1 M N ((hBR M N).1 ⟨_, hw0⟩ hbdd)
      have hz'eq : z' = O.brmax M N := by rw [hz', if_pos hB]
      obtain ⟨⟨hyF, hygr⟩, hyext⟩ := hbr
      have hy1 : lam ≤ (O.brmax M N).1 := hygr.2 ⟨(lam, p), hw0, rfl⟩
      have hy2 : (O.brmax M N).1 < s.hi := hBnd _ hyF
      have hy3 : (O.brmax M N).1 < (O.brmax M N).2.1 ⬝ᵥ a := hC _ hyF hy1
      refine ⟨⟨hp, ⟨⟨⟨hzF, hz1, hz2⟩, hzgr⟩, hzext⟩, fun _ => ⟨⟨hyF, hygr⟩, hyext⟩⟩, Or.inr ?_⟩
      rw [hz'eq]
      refine ⟨fun h => by simp only at h; linarith, by linarith, ⟨hy2.le, ⟨_, face_opt A b lam hY _ hyF,
        hy3.le⟩, ⟨pH, hpH, hpHa⟩⟩, by simp only; linarith, ⟨M, N, hyext⟩, Or.inr rfl, Or.inl rfl⟩
    · have hz'eq : z' = z := by rw [hz', if_neg hB]
      have heq : z.2.1 ⬝ᵥ a = z.1 := by push Not at hB; linarith
      refine ⟨⟨hp, ⟨⟨⟨hzF, hz1, hz2⟩, hzgr⟩, hzext⟩, fun h => absurd h hB⟩, Or.inl ?_⟩
      rw [hz'eq]
      exact ⟨heq, Or.inl hzext, face_opt A b lam hY z hzF⟩
  · -- Case B: Pmin
    have hA' : p.1 ⬝ᵥ a ≤ lam := by push Not at hA; exact hA.le
    have hfe : (PminFeas A a b M N lam).Nonempty := ⟨(lam, p), hw0, hA', le_refl _⟩
    have hwE : w ∈ PminExtreme A a b M N lam := hadm.2.2.2.1 M N lam ((hPM M N lam).2 hfe)
    obtain ⟨⟨⟨hwF, hw1, hw2⟩, hwle⟩, hwext⟩ := hwE
    rw [hS, if_neg hA, if_neg hA]
    by_cases hB : w.2.1 ⬝ᵥ a < w.1
    · have hC : ∀ u ∈ PFace A b M N, u.1 ≤ lam → u.2.1 ⬝ᵥ a < u.1 := by
        intro u hu hl
        by_contra hcon
        push Not at hcon
        obtain ⟨t1, t2, ht1, ht2, hts, hte⟩ :=
          combo (u.2.1 ⬝ᵥ a - u.1) (p.1 ⬝ᵥ a - lam) (by linarith) (by linarith)
        have hv := hconv hu hw0 ht1 ht2 hts
        have hv1 := combo_fst u ((lam, p) : PolyPoint m n) t1 t2
        have hv2 := combo_dot u ((lam, p) : PolyPoint m n) t1 t2 a
        simp only at hv1 hv2
        have hfeas : t1 • u + t2 • ((lam, p) : PolyPoint m n) ∈ PminFeas A a b M N lam := by
          refine ⟨hv, ?_, ?_⟩
          · rw [hv1, hv2]; linear_combination hte
          · rw [hv1]
            have e : t1 * lam + t2 * lam = lam := by linear_combination lam * hts
            have := mul_nonneg ht1 (sub_nonneg.2 hl)
            nlinarith
        have := hwle.2 ⟨_, hfeas, rfl⟩
        simp only at this
        rw [hv1, hv2] at this
        have h0 : t1 * u.1 + t2 * lam - (t1 * (u.2.1 ⬝ᵥ a) + t2 * (p.1 ⬝ᵥ a)) = 0 := by
          linear_combination (-1 : ℝ) * hte
        linarith
      have hBnd : ∀ u ∈ PFace A b M N, s.lo < u.1 := by
        intro u hu
        by_contra hcon
        push Not at hcon
        obtain ⟨t1, t2, ht1, ht2, hts, hte⟩ :=
          combo (lam - s.lo) (u.1 - s.lo) (by linarith) (by linarith)
        have hv := hconv hw0 hu ht1 ht2 hts
        have hv1 := combo_fst ((lam, p) : PolyPoint m n) u t1 t2
        simp only at hv1
        have hvlo : (t1 • ((lam, p) : PolyPoint m n) + t2 • u).1 = s.lo := by
          rw [hv1]; linear_combination hte + s.lo * hts
        have hpL' : pL ∈ POpt A b (t1 • ((lam, p) : PolyPoint m n) + t2 • u).1 := by
          rw [hvlo]; exact hpL
        have hc := face_contains A b lam hY _ hv pL hpL'
        have := hC _ hc (by simp only; rw [hvlo]; exact hlo_lam)
        simp only at this
        rw [hvlo] at this
        linarith
      have hbdd : BddBelow ((fun q : PolyPoint m n => q.1) '' PFace A b M N) := by
        refine ⟨s.lo, ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        exact (hBnd u hu).le
      have hbr : O.brmin M N ∈ BRminExtreme A b M N :=
        hadm.2.2.2.2.2 M N ((hBR M N).2 ⟨_, hw0⟩ hbdd)
      have hw'eq : w' = O.brmin M N := by rw [hw', if_pos hB]
      obtain ⟨⟨hyF, hygr⟩, hyext⟩ := hbr
      have hy1 : (O.brmin M N).1 ≤ lam := hygr.2 ⟨(lam, p), hw0, rfl⟩
      have hy2 : s.lo < (O.brmin M N).1 := hBnd _ hyF
      have hy3 : (O.brmin M N).2.1 ⬝ᵥ a < (O.brmin M N).1 := hC _ hyF hy1
      refine ⟨⟨hp, ⟨⟨⟨hwF, hw1, hw2⟩, hwle⟩, hwext⟩, fun _ => ⟨⟨hyF, hygr⟩, hyext⟩⟩, Or.inr ?_⟩
      rw [hw'eq]
      refine ⟨fun h => by simp only at h; linarith, by linarith, ⟨hy2.le, ⟨pL, hpL, hpLa⟩,
        ⟨_, face_opt A b lam hY _ hyF, hy3.le⟩⟩, by simp only; linarith, ⟨M, N, hyext⟩,
        Or.inl rfl, Or.inr rfl⟩
    · have hw'eq : w' = w := by rw [hw', if_neg hB]
      have heq : w.2.1 ⬝ᵥ a = w.1 := by push Not at hB; linarith
      refine ⟨⟨hp, ⟨⟨⟨hwF, hw1, hw2⟩, hwle⟩, hwext⟩, fun h => absurd h hB⟩, Or.inl ?_⟩
      rw [hw'eq]
      exact ⟨heq, Or.inr hwext, face_opt A b lam hY w hwF⟩

end R1BSAux

open Matrix RankOneBimatrix.BinSearch

namespace R1BSAux

lemma poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

lemma size_mul_le (x y : ℕ) : Nat.size (x * y) ≤ Nat.size x + Nat.size y := by
  rw [Nat.size_le, pow_add]
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp
  · exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self x) (Nat.lt_size_self y).le
      (by positivity)

lemma size_add_le (x y : ℕ) : Nat.size (x + y) ≤ Nat.size x + Nat.size y + 1 := by
  rw [Nat.size_le]
  have h1 := Nat.lt_size_self x
  have h2 := Nat.lt_size_self y
  have h3 : 2 ^ Nat.size x ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ Nat.size y ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

lemma ratSize_div_le (N : ℤ) (D : ℕ) (hD : 0 < D) :
    ratSize ((N : ℚ) / (D : ℚ)) ≤ 1 + Nat.size N.natAbs + Nat.size D := by
  have hq : ((N : ℚ) / (D : ℚ)) = Rat.divInt N (D : ℤ) := by
    rw [Rat.divInt_eq_div]; push_cast; rfl
  rw [hq]
  have hD' : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hden : (Rat.divInt N (D : ℤ)).den ≤ D := by
    have := Rat.den_dvd N (D : ℤ)
    have h2 : ((Rat.divInt N (D : ℤ)).den : ℤ) ≤ (D : ℤ) := Int.le_of_dvd (by exact_mod_cast hD) this
    exact_mod_cast h2
  have hnum : (Rat.divInt N (D : ℤ)).num.natAbs ≤ N.natAbs := by
    rcases eq_or_ne N 0 with h0 | h0
    · subst h0; simp
    · have := Rat.num_dvd N hD'
      exact Nat.le_of_dvd (Int.natAbs_pos.2 h0) (Int.natAbs_dvd_natAbs.2 this)
  unfold ratSize
  have := Nat.size_le_size hden
  have := Nat.size_le_size hnum
  omega

lemma ratSize_avg_le (q1 q2 : ℚ) :
    ratSize ((q1 + q2) / 2) ≤ 4 * (ratSize q1 + ratSize q2) := by
  set N : ℤ := q1.num * q2.den + q2.num * q1.den with hN
  set D : ℕ := 2 * q1.den * q2.den with hD
  have hDpos : 0 < D := by positivity
  have heq : (q1 + q2) / 2 = (N : ℚ) / (D : ℚ) := by
    have e1 := Rat.num_div_den q1
    have e2 := Rat.num_div_den q2
    have h1 : (q1.den : ℚ) ≠ 0 := by positivity
    have h2 : (q2.den : ℚ) ≠ 0 := by positivity
    rw [hN, hD]; push_cast
    rw [← e1, ← e2]
    field_simp
    rw [e1, e2]
    ring
  rw [heq]
  refine (ratSize_div_le N D hDpos).trans ?_
  have hNabs : N.natAbs ≤ q1.num.natAbs * q2.den + q2.num.natAbs * q1.den := by
    rw [hN]
    refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp
  have s1 := Nat.size_le_size hNabs
  have s2 := size_add_le (q1.num.natAbs * q2.den) (q2.num.natAbs * q1.den)
  have s3 := size_mul_le q1.num.natAbs q2.den
  have s4 := size_mul_le q2.num.natAbs q1.den
  have s5 : Nat.size D ≤ Nat.size 2 + Nat.size q1.den + Nat.size q2.den := by
    rw [hD]
    refine (size_mul_le _ _).trans ?_
    have := size_mul_le 2 q1.den
    omega
  have s6 : Nat.size 2 = 2 := by decide
  unfold ratSize
  omega

lemma den_lt_pow (q : ℚ) : q.den < 2 ^ ratSize q := by
  have := Nat.lt_size_self q.den
  have h : Nat.size q.den ≤ ratSize q := by unfold ratSize; omega
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h)

lemma abs_le_pow (q : ℚ) : |(q : ℝ)| ≤ 2 ^ ratSize q := by
  have hnum : (q.num.natAbs : ℝ) < 2 ^ ratSize q := by
    have := Nat.lt_size_self q.num.natAbs
    have h : Nat.size q.num.natAbs ≤ ratSize q := by unfold ratSize; omega
    have := lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) h)
    exact_mod_cast this
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [hq, abs_div]
  have : |(q.den : ℝ)| = q.den := abs_of_pos (by positivity)
  rw [this]
  have habs : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  calc (q.num.natAbs : ℝ) / q.den ≤ (q.num.natAbs : ℝ) / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ 2 ^ ratSize q := by rw [div_one]; exact hnum.le

lemma separation (q1 q2 : ℚ) (S : ℕ) (h1 : ratSize q1 ≤ S) (h2 : ratSize q2 ≤ S)
    (hne : q1 ≠ q2) : 1 / (2 : ℝ) ^ (2 * S) ≤ |(q1 : ℝ) - q2| := by
  set r := q1 - q2 with hr
  have hr0 : r ≠ 0 := sub_ne_zero.2 hne
  have hd1 : q1.den < 2 ^ S := lt_of_lt_of_le (den_lt_pow q1) (Nat.pow_le_pow_right (by norm_num) h1)
  have hd2 : q2.den < 2 ^ S := lt_of_lt_of_le (den_lt_pow q2) (Nat.pow_le_pow_right (by norm_num) h2)
  have hrd : r.den ≤ q1.den * q2.den := Nat.le_of_dvd (by positivity) (Rat.sub_den_dvd q1 q2)
  have hrd2 : r.den ≤ 2 ^ (2 * S) := by
    have : q1.den * q2.den ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hd1.le hd2.le
    rw [two_mul, pow_add]; omega
  have hcast : ((q1 : ℝ) - q2) = (r : ℝ) := by rw [hr]; push_cast; ring
  rw [hcast, Rat.cast_def r, abs_div]
  have hnum : (1 : ℝ) ≤ |(r.num : ℝ)| := by
    have : r.num ≠ 0 := Rat.num_ne_zero.2 hr0
    have := Int.one_le_abs this
    exact_mod_cast this
  have hdpos : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  rw [abs_of_pos hdpos]
  have hrd3 : (r.den : ℝ) ≤ (2 : ℝ) ^ (2 * S) := by exact_mod_cast hrd2
  calc 1 / (2 : ℝ) ^ (2 * S) ≤ 1 / (r.den : ℝ) := one_div_le_one_div_of_le hdpos hrd3
    _ ≤ |(r.num : ℝ)| / r.den := div_le_div_of_nonneg_right hnum hdpos.le

end R1BSAux

open Matrix RankOneBimatrix.BinSearch

namespace R1BSAux

variable {m n : ℕ}

theorem run_analysis (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (hstep : ∀ s : RunState m n, Inv A a b s.lo s.hi → StepOK A a b O s)
    (Good : ℝ → Prop)
    (hGood : ∀ M N z, z ∈ Set.extremePoints ℝ (PFace A b M N) → Good z.1)
    (hinit : Inv A a b (run A a b O 0).lo (run A a b O 0).hi ∧ Good (run A a b O 0).lo ∧
      Good (run A a b O 0).hi) :
    ∀ j, (∀ i < j, ¬ stop A a b O i) →
      Inv A a b (run A a b O j).lo (run A a b O j).hi ∧ Good (run A a b O j).lo ∧
      Good (run A a b O j).hi ∧
      (run A a b O j).hi - (run A a b O j).lo ≤
        ((run A a b O 0).hi - (run A a b O 0).lo) / 2 ^ j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hinit.1, hinit.2.1, hinit.2.2, by simp⟩
  | succ j ih =>
    intro hns
    obtain ⟨hinv, hgl, hgh, hlen⟩ := ih (fun i hi => hns i (Nat.lt_succ_of_lt hi))
    have hnj : ¬ stop A a b O j := hns j (Nat.lt_succ_self j)
    have hrun : run A a b O (j + 1) = step A a b O (run A a b O j) := rfl
    obtain ⟨_, hcase⟩ := hstep _ hinv
    rcases hcase with hc | hc
    · exact absurd hc.1 hnj
    · obtain ⟨_, _, hinv', hlen', ⟨M, N, hext⟩, hlo, hhi⟩ := hc
      rw [hrun]
      refine ⟨hinv', ?_, ?_, ?_⟩
      · rcases hlo with h | h
        · rw [h]; exact hgl
        · rw [h]; exact hGood M N _ hext
      · rcases hhi with h | h
        · rw [h]; exact hgh
        · rw [h]; exact hGood M N _ hext
      · rw [pow_succ, ← div_div]
        linarith [div_le_div_of_nonneg_right hlen (show (0:ℝ) ≤ 2 by norm_num)]

theorem exists_stop (A : Matrix (Fin m) (Fin n) ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (O : Oracle m n) (hstep : ∀ s : RunState m n, Inv A a b s.lo s.hi → StepOK A a b O s)
    (Good : ℝ → Prop)
    (hGood : ∀ M N z, z ∈ Set.extremePoints ℝ (PFace A b M N) → Good z.1)
    (hinit : Inv A a b (run A a b O 0).lo (run A a b O 0).hi ∧ Good (run A a b O 0).lo ∧
      Good (run A a b O 0).hi)
    (δ : ℝ) (hsep : ∀ x y, Good x → Good y → x < y → δ ≤ y - x) (T : ℕ)
    (hT : ((run A a b O 0).hi - (run A a b O 0).lo) / 2 ^ T < δ) :
    ∃ k, k ≤ T ∧ stop A a b O k := by
  by_contra hcon
  push Not at hcon
  have hns : ∀ i < T, ¬ stop A a b O i := fun i hi => hcon i hi.le
  obtain ⟨hinv, hgl, hgh, hlen⟩ := run_analysis A a b O hstep Good hGood hinit T hns
  obtain ⟨_, hcase⟩ := hstep _ hinv
  rcases hcase with hc | hc
  · exact hcon T le_rfl hc.1
  · have := hsep _ _ hgl hgh hc.2.1
    linarith

end R1BSAux

open Matrix RankOneBimatrix.BinSearch R1BSAux

lemma R1BSAux.dot_ge {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ Mixed m) (ar : Fin m → ℝ) (c : ℝ)
    (h : ∀ i, c ≤ ar i) : c ≤ x ⬝ᵥ ar := by
  obtain ⟨hx0, hx1⟩ := hx
  calc c = ∑ i, x i * c := by rw [← Finset.sum_mul, hx1, one_mul]
    _ ≤ ∑ i, x i * ar i := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hx0 i)
    _ = x ⬝ᵥ ar := rfl

lemma R1BSAux.dot_le {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ Mixed m) (ar : Fin m → ℝ) (c : ℝ)
    (h : ∀ i, ar i ≤ c) : x ⬝ᵥ ar ≤ c := by
  obtain ⟨hx0, hx1⟩ := hx
  calc x ⬝ᵥ ar = ∑ i, x i * ar i := rfl
    _ ≤ ∑ i, x i * c := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hx0 i)
    _ = c := by rw [← Finset.sum_mul, hx1, one_mul]

theorem solution :
    ∃ p : Polynomial ℕ,
      ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
        (O : Oracle m n),
        Admissible (A.map (fun r => (r : ℝ)))
          (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O →
        ∃ k : ℕ,
          k ≤ p.eval (inputSize A a b) ∧
          stop (A.map (fun r => (r : ℝ))) (fun i => (a i : ℝ))
            (fun j => (b j : ℝ)) O k ∧
          (∀ j < k, ¬ stop (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j) ∧
          (∀ j ≤ k, callsGenuine (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j) ∧
          (∀ j ≤ k, ∃ q : ℚ,
            (q : ℝ) = midpoint (A.map (fun r => (r : ℝ)))
              (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j ∧
            ratSize q ≤ p.eval (inputSize A a b)) ∧
          (∀ j ≤ k, ∃ q : ℚ,
            (q : ℝ) = lamStar (A.map (fun r => (r : ℝ)))
              (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j ∧
            ratSize q ≤ p.eval (inputSize A a b)) ∧
          O.dual (lamStar (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) ∈
            DExtreme (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ))
              (lamStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) ∧
          (∀ y t, (y, t) ∈ Yopt (A.map (fun r => (r : ℝ)))
              (fun j => (b j : ℝ))
              (lamStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) →
            IsNE (A.map (fun r => (r : ℝ)))
              (rankOneB (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)))
              (xStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) y) := by
  classical
  obtain ⟨pv, hpv⟩ := extreme_lambda_size
  refine ⟨Polynomial.X + 2 + 2 * (pv + Polynomial.X) + 8 * (pv + Polynomial.X) +
    pv.comp (Polynomial.X + 8 * (pv + Polynomial.X)), ?_⟩
  intro m n hm hn A a b O hadm
  set Ar : Matrix (Fin m) (Fin n) ℝ := A.map (fun r => (r : ℝ)) with hAr
  set ar : Fin m → ℝ := fun i => (a i : ℝ) with har
  set br : Fin n → ℝ := fun j => (b j : ℝ) with hbr
  set L := inputSize A a b with hL
  set S0 := pv.eval L + L with hS0
  have hpeval : (Polynomial.X + 2 + 2 * (pv + Polynomial.X) + 8 * (pv + Polynomial.X) +
      pv.comp (Polynomial.X + 8 * (pv + Polynomial.X))).eval L =
      L + 2 + 2 * S0 + 8 * S0 + pv.eval (L + 8 * S0) := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, hS0]
  rw [hpeval]
  have hstep : ∀ s : RunState m n, Inv Ar ar br s.lo s.hi → StepOK Ar ar br O s :=
    fun s hs => step_spec Ar ar br O hadm (fun l => primal_extreme_exists hm hn Ar br l)
      (fun l => dual_extreme_exists hm hn Ar br l) (fun l => strong_duality hm hn Ar br l)
      (fun M N l => pmax_pmin_extreme_exists hm hn Ar ar br M N l)
      (fun M N => br_extreme_exists hm hn Ar br M N) s hs
  let Good : ℝ → Prop := fun x => ∃ q : ℚ, (q : ℝ) = x ∧ ratSize q ≤ S0
  have hGood : ∀ M N z, z ∈ Set.extremePoints ℝ (PFace Ar br M N) → Good z.1 := by
    intro M N z hz
    obtain ⟨q, hq, hs⟩ := (hpv m n hm hn A a b M N 0).1 z hz
    change ratSize q ≤ pv.eval L at hs
    exact ⟨q, hq, by omega⟩
  have ha_size : ∀ i, ratSize (a i) ≤ L := by
    intro i
    have h1 : ratSize (a i) ≤ ∑ i, ratSize (a i) :=
      Finset.single_le_sum (f := fun i => ratSize (a i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : L = (∑ i : Fin m, ∑ j : Fin n, ratSize (A i j)) +
      (∑ i : Fin m, ratSize (a i)) + ∑ j : Fin n, ratSize (b j) := rfl
    omega
  have hfin : (Set.range ar).Finite := Set.finite_range ar
  have hne : (Set.range ar).Nonempty := ⟨ar ⟨0, hm⟩, ⟨_, rfl⟩⟩
  obtain ⟨i0, hi0⟩ := hne.csInf_mem hfin
  obtain ⟨i1, hi1⟩ := hne.csSup_mem hfin
  have hlo_le : ∀ i, sInf (Set.range ar) ≤ ar i := fun i => csInf_le hfin.bddBelow ⟨i, rfl⟩
  have hhi_ge : ∀ i, ar i ≤ sSup (Set.range ar) := fun i => le_csSup hfin.bddAbove ⟨i, rfl⟩
  have hlo0 : (run Ar ar br O 0).lo = sInf (Set.range ar) := rfl
  have hhi0 : (run Ar ar br O 0).hi = sSup (Set.range ar) := rfl
  have hinit : Inv Ar ar br (run Ar ar br O 0).lo (run Ar ar br O 0).hi ∧
      Good (run Ar ar br O 0).lo ∧ Good (run Ar ar br O 0).hi := by
    rw [hlo0, hhi0]
    refine ⟨⟨(hlo_le i0).trans (hhi_ge i0), ?_, ?_⟩, ⟨a i0, hi0, by have := ha_size i0; omega⟩,
      ⟨a i1, hi1, by have := ha_size i1; omega⟩⟩
    · obtain ⟨p0, hp0⟩ := primal_extreme_exists hm hn Ar br (sInf (Set.range ar))
      exact ⟨p0, hp0.1, dot_ge _ hp0.1.1.1 ar _ hlo_le⟩
    · obtain ⟨p0, hp0⟩ := primal_extreme_exists hm hn Ar br (sSup (Set.range ar))
      exact ⟨p0, hp0.1, dot_le _ hp0.1.1.1 ar _ hhi_ge⟩
  have hsep : ∀ x y, Good x → Good y → x < y → 1 / (2 : ℝ) ^ (2 * S0) ≤ y - x := by
    rintro x y ⟨q1, rfl, h1⟩ ⟨q2, rfl, h2⟩ hlt
    have hne : q2 ≠ q1 := by
      intro h; rw [h] at hlt; exact lt_irrefl _ hlt
    have := separation q2 q1 S0 h2 h1 hne
    rwa [abs_of_pos (by linarith)] at this
  have hD0 : (run Ar ar br O 0).hi - (run Ar ar br O 0).lo ≤ 2 ^ (L + 1) := by
    rw [hlo0, hhi0, ← hi0, ← hi1]
    have e1 := abs_le_pow (a i0)
    have e2 := abs_le_pow (a i1)
    have f1 : (2 : ℝ) ^ ratSize (a i0) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (ha_size i0)
    have f2 : (2 : ℝ) ^ ratSize (a i1) ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (ha_size i1)
    have g1 := neg_abs_le ((a i0 : ℚ) : ℝ)
    have g2 := le_abs_self ((a i1 : ℚ) : ℝ)
    simp only [har]
    rw [pow_succ]
    linarith
  have hT : ((run Ar ar br O 0).hi - (run Ar ar br O 0).lo) / 2 ^ (L + 2 + 2 * S0) <
      1 / (2 : ℝ) ^ (2 * S0) := by
    have hpos : (0 : ℝ) < 2 ^ (2 * S0) := by positivity
    have hpos2 : (0 : ℝ) < 2 ^ (L + 1) := by positivity
    rw [div_lt_div_iff₀ (by positivity) hpos]
    have : (2 : ℝ) ^ (L + 2 + 2 * S0) = 2 ^ (L + 1) * 2 ^ (2 * S0) * 2 := by
      rw [← pow_add, ← pow_succ]; ring_nf
    rw [this]
    nlinarith
  obtain ⟨k0, hk0T, hk0⟩ := exists_stop Ar ar br O hstep Good hGood hinit _ hsep _ hT
  have hex : ∃ k, stop Ar ar br O k := ⟨k0, hk0⟩
  set k := Nat.find hex with hkdef
  have hk : stop Ar ar br O k := Nat.find_spec hex
  have hkmin : ∀ j < k, ¬ stop Ar ar br O j := fun j hj => Nat.find_min hex hj
  have hkT : k ≤ L + 2 + 2 * S0 := (Nat.find_min' hex hk0).trans hk0T
  have hinfo : ∀ j ≤ k, Inv Ar ar br (run Ar ar br O j).lo (run Ar ar br O j).hi ∧
      Good (run Ar ar br O j).lo ∧ Good (run Ar ar br O j).hi := by
    intro j hj
    obtain ⟨h1, h2, h3, _⟩ := run_analysis Ar ar br O hstep Good hGood hinit j
      (fun i hi => hkmin i (lt_of_lt_of_le hi hj))
    exact ⟨h1, h2, h3⟩
  have hmid : ∀ j ≤ k, ∃ q : ℚ, (q : ℝ) = midpoint Ar ar br O j ∧ ratSize q ≤ 8 * S0 := by
    intro j hj
    obtain ⟨_, ⟨q1, hq1, hs1⟩, ⟨q2, hq2, hs2⟩⟩ := hinfo j hj
    refine ⟨(q1 + q2) / 2, ?_, ?_⟩
    · show _ = ((run Ar ar br O j).lo + (run Ar ar br O j).hi) / 2
      rw [← hq1, ← hq2]; push_cast; ring
    · have := ratSize_avg_le q1 q2
      omega
  -- the stopping iteration
  obtain ⟨_, hcasek⟩ := hstep _ (hinfo k le_rfl).1
  have hstopk : (step Ar ar br O (run Ar ar br O k)).sol.2.1 ⬝ᵥ ar =
      (step Ar ar br O (run Ar ar br O k)).sol.1 := hk
  rcases hcasek with hck | hck
  swap
  · exact absurd hstopk hck.1
  obtain ⟨_, hextk, hoptk⟩ := hck
  refine ⟨k, by omega, hk, hkmin, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [callsGenuine_eq]
    exact (hstep _ (hinfo j hj).1).1
  · intro j hj
    obtain ⟨q, hq, hs⟩ := hmid j hj
    exact ⟨q, hq, by omega⟩
  · intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · obtain ⟨_, hcase⟩ := hstep _ (hinfo j hj).1
      rcases hcase with hc | hc
      · exact absurd hc.1 (hkmin j hlt)
      · obtain ⟨M, N, hext⟩ := hc.2.2.2.2.1
        obtain ⟨q, hq, hs⟩ := hGood M N _ hext
        exact ⟨q, hq, by omega⟩
    · subst heq
      obtain ⟨qm, hqm, hsm⟩ := hmid k le_rfl
      have hqm' : ((run Ar ar br O k).lo + (run Ar ar br O k).hi) / 2 = (qm : ℝ) := hqm.symm
      rw [hqm'] at hextk
      have hmono := poly_eval_mono pv (show L + ratSize qm ≤ L + 8 * S0 by omega)
      rcases hextk with he | he
      · obtain ⟨q, hq, hs⟩ := (hpv m n hm hn A a b _ _ qm).2.1 _ he
        change ratSize q ≤ pv.eval (L + ratSize qm) at hs
        exact ⟨q, hq, by omega⟩
      · obtain ⟨q, hq, hs⟩ := (hpv m n hm hn A a b _ _ qm).2.2 _ he
        change ratSize q ≤ pv.eval (L + ratSize qm) at hs
        exact ⟨q, hq, by omega⟩
  · exact hadm.2.1 _ (dual_extreme_exists hm hn Ar br _)
  · intro y t hyt
    exact ((lemma_9 hm hn Ar ar br _ _ y).2 t _ _ hyt hoptk hstopk).1

