-- Prove2me | solution 1 for RobustPMI.Hierarchy.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:45:45.727658+00:00
-- url     : https://prove2.me/submissions/009b07a6-45b4-454d-b2fb-a6ab93883dfc

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Theorems.Thm_RobustPMI_Hierarchy_proposition_4_7

set_option linter.unusedSectionVars false

namespace RobustPMI.Hierarchy.P41aux
open MvPolynomial Matrix RobustPMI.Hierarchy

section Basic
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def dirac (y : σ → ℝ) : (σ →₀ ℕ) → ℝ := fun α => eval y (monomial α (1 : ℝ))

lemma Hs_eq_of_subset (v : (σ →₀ ℕ) → ℝ) (h : MvPolynomial σ ℝ) (B : Finset (σ →₀ ℕ))
    (hB : h.support ⊆ B) : Hs v h = ∑ α ∈ B, coeff α h * v α := by
  unfold Hs
  refine Finset.sum_subset hB ?_
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]

lemma Hs_dirac (y : σ → ℝ) (h : MvPolynomial σ ℝ) : Hs (dirac y) h = eval y h := by
  conv_rhs => rw [h.as_sum]
  rw [map_sum]
  unfold Hs dirac
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [show monomial α (coeff α h) = C (coeff α h) * monomial α 1 by
    rw [C_mul_monomial, mul_one]]
  rw [map_mul, eval_C]

lemma dirac_add (y : σ → ℝ) (α β : σ →₀ ℕ) : dirac y (α + β) = dirac y α * dirac y β := by
  unfold dirac
  rw [← map_mul, monomial_mul, one_mul]

lemma dirac_zero (y : σ → ℝ) : dirac y 0 = 1 := by
  simp [dirac]

lemma sE_dirac (y : σ → ℝ) : sE (dirac y) = y := by
  funext j
  simp [sE, dirac, ← X.eq_1]

lemma Hs_lin (v w : (σ →₀ ℕ) → ℝ) (t u : ℝ) (h : MvPolynomial σ ℝ) :
    Hs (fun α => t * v α + u * w α) h = t * Hs v h + u * Hs w h := by
  unfold Hs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => by ring

lemma dirac_single (y : σ → ℝ) (j : σ) : dirac y (Finsupp.single j 1) = y j := by
  have := congrFun (sE_dirac y) j
  simpa [sE] using this

lemma momentMat_dirac_psd (y : σ → ℝ) (D : ℕ) :
    (momentMat D (scalarSeq (dirac y))).PosSemidef := by
  have : momentMat D (scalarSeq (dirac y)) =
      vecMulVec (fun p : (monos (σ := σ) D) × Fin 1 => dirac y p.1.1)
        (star fun p : (monos (σ := σ) D) × Fin 1 => dirac y p.1.1) := by
    ext p p'
    simp [momentMat, scalarSeq, vecMulVec, dirac_add]
  rw [this]
  exact posSemidef_vecMulVec_self_star _

lemma momentMat_lin (D : ℕ) (v w : (σ →₀ ℕ) → ℝ) (t u : ℝ) :
    momentMat D (scalarSeq (fun α => t * v α + u * w α)) =
      t • momentMat D (scalarSeq v) + u • momentMat D (scalarSeq w) := by
  ext p p'
  simp [momentMat, scalarSeq]

lemma momentMat_two_psd (a b : σ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (D : ℕ) :
    (momentMat D (scalarSeq (fun α => t * dirac a α + (1 - t) * dirac b α))).PosSemidef := by
  rw [momentMat_lin]
  exact ((momentMat_dirac_psd a D).smul ht0).add ((momentMat_dirac_psd b D).smul (by linarith))

end Basic

section Jensen
variable {ℓ n m q s : ℕ}

lemma degMat_scalar (h : MvPolynomial (Fin ℓ) ℝ) :
    degMat (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) = h.totalDegree := by
  simp only [degMat, of_apply]
  exact Finset.sup_const Finset.univ_nonempty _

lemma quadForm_scalar (h : MvPolynomial (Fin ℓ) ℝ) (v : Fin 1 → ℝ) :
    quadForm (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) v = C (v 0 * v 0) * h := by
  simp [quadForm, C_mul]
  ring

lemma isPSDSOSConvex_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) :
    IsPSDSOSConvex (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) := by
  intro v
  obtain ⟨l, T, hT⟩ := hh
  refine ⟨l, T.map (fun p => C (v 0) * p), ?_⟩
  rw [quadForm_scalar]
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun hT i) j
  simp only [hessian, of_apply] at hij ⊢
  rw [pderiv_C_mul, pderiv_C_mul, hij]
  simp only [mul_apply, transpose_apply, map_apply, Finset.mul_sum, C_mul]
  refine Finset.sum_congr rfl fun r _ => by ring

lemma jensen_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (v : (Fin ℓ →₀ ℕ) → ℝ)
    (hv0 : v 0 = 1) (hM : (momentMat ((h.totalDegree + 1) / 2) (scalarSeq v)).PosSemidef) :
    eval (sE v) h ≤ Hs v h := by
  have H := proposition_4_7 (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => h) (by ext i j; rfl)
    (isPSDSOSConvex_scalar h hh) v hv0 (by rw [degMat_scalar]; exact hM)
  have := H.diag_nonneg (i := 0)
  simpa [sub_nonneg] using this

lemma two_point_facts (a b : Fin ℓ → ℝ) (t : ℝ) :
    let v : (Fin ℓ →₀ ℕ) → ℝ := fun α => t * dirac a α + (1 - t) * dirac b α
    v 0 = 1 ∧ sE v = t • a + (1 - t) • b ∧
      ∀ h : MvPolynomial (Fin ℓ) ℝ, Hs v h = t * eval a h + (1 - t) * eval b h := by
  intro v
  refine ⟨by simp [v, dirac_zero], ?_, fun h => by simp only [v]; rw [Hs_lin, Hs_dirac, Hs_dirac]⟩
  funext j
  simp [v, sE, dirac_single]

lemma jensen2_scalar (h : MvPolynomial (Fin ℓ) ℝ) (hh : IsSOSConvex h) (a b : Fin ℓ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eval (t • a + (1 - t) • b) h ≤ t * eval a h + (1 - t) * eval b h := by
  obtain ⟨h0, hE, hH⟩ := two_point_facts a b t
  have := jensen_scalar h hh _ h0 (momentMat_two_psd a b t ht0 ht1 _)
  rwa [hE, hH] at this

lemma jensen2_mat {m : ℕ} (Q : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ) ℝ)) (hQ : Q.IsSymm)
    (hc : IsPSDSOSConvex Q) (a b : Fin ℓ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • Q.map (eval a) + (1 - t) • Q.map (eval b) - Q.map (eval (t • a + (1 - t) • b))).PosSemidef := by
  obtain ⟨h0, hE, hH⟩ := two_point_facts a b t
  have H := proposition_4_7 Q hQ hc _ h0 (momentMat_two_psd a b t ht0 ht1 _)
  rw [hE] at H
  convert H using 2
  ext i j
  simp [hH]

lemma eval_aeval_Patx (y : Fin ℓ → ℝ) (x : Fin n → ℝ) (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) :
    eval y (aeval (Sum.elim (X : Fin ℓ → MvPolynomial (Fin ℓ) ℝ) fun i => C (x i)) p) =
      eval (Sum.elim y x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_eq, eval_C, eval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]
    rcases i with j | j <;> simp

lemma Patx_map_eval (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) (x : Fin n → ℝ) : (Patx P x).map (eval y) = evalP P y x := by
  ext i j
  simp only [Patx, evalP, map_apply]
  exact eval_aeval_Patx y x _

lemma Patx_symm (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) : (Patx P x).IsSymm := by
  unfold Patx
  rw [IsSymm, ← transpose_map, hP.eq]

lemma evalP_concave (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) (hc : IsPSDSOSConvex (-(Patx P x))) (a b : Fin ℓ → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (evalP P (t • a + (1 - t) • b) x - (t • evalP P a x + (1 - t) • evalP P b x)).PosSemidef := by
  have H := jensen2_mat (-(Patx P x)) (Patx_symm P hP x).neg hc a b t ht0 ht1
  have e : ∀ y, (-(Patx P x)).map (eval y) = -(evalP P y x) := fun y => by
    rw [← Patx_map_eval]; ext i j; simp
  rw [e, e, e] at H
  convert H using 1
  simp only [smul_neg]
  abel

lemma evalP_isHermitian (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (hP : P.IsSymm) (y : Fin ℓ → ℝ) (x : Fin n → ℝ) : (evalP P y x).IsHermitian := by
  unfold evalP
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← transpose_map, hP.eq]

lemma continuous_eval_elim (p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ) (x : Fin n → ℝ) :
    Continuous fun y : Fin ℓ → ℝ => eval (Sum.elim y x) p := by
  refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
  rcases i with j | j
  · exact continuous_apply j
  · exact continuous_const

lemma fstar_eq (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (y : Fin ℓ → ℝ)
    (hy : IsGlobalMin f θ P G y) : fstar f θ P G = eval y f := by
  unfold fstar
  refine IsLeast.csInf_eq ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

end Jensen

section Lagr
variable {ℓ : ℕ}

/-- Lagrange multipliers for a convex program with finitely many concave constraints over a
convex set, under Slater's condition (separation in `ℝ × ℝ^ι`). -/
lemma lagrange_gen {ι : Type} [Fintype ι] (Z : Set (Fin ℓ → ℝ))
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • a + (1 - t) • b ∈ Z)
    (F : (Fin ℓ → ℝ) → ℝ)
    (hF : ∀ a ∈ Z, ∀ b ∈ Z, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → F (t • a + (1 - t) • b) ≤ t * F a + (1 - t) * F b)
    (c : ι → (Fin ℓ → ℝ) → ℝ)
    (hc : ∀ i, ∀ a ∈ Z, ∀ b ∈ Z, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      t * c i a + (1 - t) * c i b ≤ c i (t • a + (1 - t) • b))
    (yb : Fin ℓ → ℝ) (hybZ : yb ∈ Z) (hyb : ∀ i, 0 < c i yb) (gs : ℝ)
    (hmin : ∀ y ∈ Z, (∀ i, 0 ≤ c i y) → gs ≤ F y) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∀ y ∈ Z, ∑ i, lam i * c i y ≤ F y - gs := by
  classical
  set A : Set (ℝ × (ι → ℝ)) :=
    {p | ∃ y ∈ Z, F y - gs < p.1 ∧ ∀ i, -c i y < p.2 i} with hAdef
  set Bs : Set (ℝ × (ι → ℝ)) := {p | p.1 ≤ 0 ∧ ∀ i, p.2 i ≤ 0} with hBdef
  have hAconv : Convex ℝ A := by
    rintro p ⟨y1, hy1, h11, h12⟩ q ⟨y2, hy2, h21, h22⟩ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    refine ⟨a • y1 + (1 - a) • y2, hZ y1 hy1 y2 hy2 a ha (by linarith), ?_, fun i => ?_⟩
    · have J := hF y1 hy1 y2 hy2 a ha (by linarith)
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rcases ha.lt_or_eq with ha' | ha'
      · have k1 : a * (F y1 - gs) < a * p.1 := mul_lt_mul_of_pos_left h11 ha'
        have k2 : (1 - a) * (F y2 - gs) ≤ (1 - a) * q.1 := mul_le_mul_of_nonneg_left h21.le hb
        nlinarith
      · subst ha'; simp at J ⊢; linarith
    · have J := hc i y1 hy1 y2 hy2 a ha (by linarith)
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1j := h12 i; have h2j := h22 i
      rcases ha.lt_or_eq with ha' | ha'
      · have k1 := mul_lt_mul_of_pos_left h1j ha'
        have k2 := mul_le_mul_of_nonneg_left h2j.le hb
        nlinarith
      · subst ha'; simp at J ⊢; linarith
  have hAopen : IsOpen A := by
    have : A = ⋃ y ∈ Z, ({p : ℝ × (ι → ℝ) | F y - gs < p.1} ∩
        ⋂ i, {p : ℝ × (ι → ℝ) | -c i y < p.2 i}) := by
      ext p
      constructor
      · rintro ⟨y, hy, h1, h2⟩
        exact Set.mem_biUnion hy ⟨h1, Set.mem_iInter.2 h2⟩
      · intro hp
        simp only [Set.mem_iUnion] at hp
        obtain ⟨y, hy, h1, h2⟩ := hp
        exact ⟨y, hy, h1, Set.mem_iInter.1 h2⟩
    rw [this]
    exact isOpen_biUnion fun y _ => (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        ((continuous_apply i).comp continuous_snd))
  have hBconv : Convex ℝ Bs := by
    rintro p ⟨h11, h12⟩ q ⟨h21, h22⟩ a b ha hb hab
    refine ⟨?_, fun i => ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := h12 i; have := h22 i; nlinarith
  have hdisj : Disjoint A Bs := by
    refine Set.disjoint_left.2 fun p hpA hpB => ?_
    obtain ⟨y, hyZ, h1, h2⟩ := hpA
    have := hmin y hyZ fun i => by have := h2 i; have := hpB.2 i; linarith
    linarith [hpB.1]
  obtain ⟨f, u, hfA, hfB⟩ := geometric_hahn_banach_open hAconv hAopen hBconv hdisj
  have hfB0 : ∀ b ∈ Bs, 0 ≤ f b := by
    intro b hb
    by_contra hneg
    push Not at hneg
    set cc := (|u| + 1) / (-f b)
    have hc0 : 0 < cc := div_pos (by positivity) (by linarith)
    have hcb : cc • b ∈ Bs := ⟨by simp only [Prod.smul_fst, smul_eq_mul]; nlinarith [hb.1],
      fun j => by simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; nlinarith [hb.2 j]⟩
    have := hfB _ hcb
    rw [map_smul, smul_eq_mul] at this
    have e : cc * f b = -(|u| + 1) := by
      simp only [cc]; field_simp [hneg.ne]
    rw [e] at this
    linarith [le_abs_self u, neg_abs_le u]
  have hu0 : u ≤ 0 := by simpa using hfB 0 ⟨le_rfl, fun _ => le_rfl⟩
  set μ0 := f (1, 0)
  set μ : ι → ℝ := fun j => f (0, Pi.single j 1)
  have hrep : ∀ p : ℝ × (ι → ℝ), f p = μ0 * p.1 + ∑ j, μ j * p.2 j := by
    intro p
    have hp : p = p.1 • ((1 : ℝ), (0 : ι → ℝ)) + ∑ j, p.2 j • ((0 : ℝ), (Pi.single j (1 : ℝ))) := by
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, μ0, μ]
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hμ0 : μ0 ≤ 0 := by
    have := hfB0 (-1, 0) ⟨by norm_num, fun _ => le_rfl⟩
    rw [hrep] at this; simpa using this
  have hμ : ∀ j, μ j ≤ 0 := fun j => by
    have := hfB0 (0, -Pi.single j 1) ⟨le_rfl, fun i => by
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]⟩
    rw [hrep] at this
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  have hineq : ∀ y ∈ Z, ∑ j, (-μ j) * c j y ≤ (-μ0) * (F y - gs) := by
    intro y hyZ
    set K := -μ0 + ∑ j, -μ j
    have hK : 0 ≤ K := by
      have : 0 ≤ ∑ j, -μ j := Finset.sum_nonneg fun j _ => by linarith [hμ j]
      linarith
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set ε := δ / (K + 1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    have hmem : (F y - gs + ε, fun j => -c j y + ε) ∈ A :=
      ⟨y, hyZ, by simp; linarith, fun j => by simp; linarith⟩
    have h1 := hfA _ hmem
    rw [hrep] at h1
    simp only at h1
    have h2 : ε * K < δ := by
      simp only [ε]; rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    have e : μ0 * (F y - gs + ε) + ∑ j, μ j * (-c j y + ε) =
        -((-μ0) * (F y - gs) - ∑ j, (-μ j) * c j y) - ε * K := by
      simp only [K, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
      ring_nf
      simp only [Finset.sum_neg_distrib, Finset.mul_sum]
      ring_nf
    rw [e] at h1
    linarith
  have hν0 : 0 < -μ0 := by
    rcases (neg_nonneg.2 hμ0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hineq yb hybZ
      rw [← h, zero_mul] at h0
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ (-μ j) * c j yb := fun j _ =>
        mul_nonneg (by linarith [hμ j]) (hyb j).le
      have hterm : ∀ j, (-μ j) * c j yb = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h0 (Finset.sum_nonneg hnn)) j
          (Finset.mem_univ _)
      have hμz : ∀ j, μ j = 0 := fun j => by
        rcases mul_eq_zero.1 (hterm j) with h1 | h1
        · linarith
        · exact absurd h1 (hyb j).ne'
      have hμ00 : μ0 = 0 := by linarith
      have hf0 : ∀ p, f p = 0 := fun p => by
        rw [hrep]; simp [hμz, hμ00]
      have hmem : (F yb - gs + 1, fun j => -c j yb + 1) ∈ A :=
        ⟨yb, hybZ, by simp, fun j => by simp⟩
      have := hfA _ hmem
      rw [hf0] at this
      have := hfB0 0 ⟨le_rfl, fun _ => le_rfl⟩
      have := hfB 0 ⟨le_rfl, fun _ => le_rfl⟩
      rw [hf0] at this
      linarith
  refine ⟨fun j => (-μ j) / (-μ0), fun j => div_nonneg (by linarith [hμ j]) hν0.le,
    fun y hyZ => ?_⟩
  have := hineq y hyZ
  rw [show ∑ j, (-μ j) / (-μ0) * c j y = (∑ j, (-μ j) * c j y) / (-μ0) by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring]
  rw [div_le_iff₀ hν0]
  linarith

end Lagr

section Cval
variable {ℓ n m q s : ℕ}

/-- `vᵀ P(y, x) v`. -/
noncomputable def cval (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (v : Fin m → ℝ) (y : Fin ℓ → ℝ) : ℝ :=
  ∑ a, ∑ b, v a * evalP P y x a b * v b

lemma quad_eq (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    star v ⬝ᵥ (M *ᵥ v) = ∑ a, ∑ b, v a * M a b * v b := by
  simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma cval_concave (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) (hc : IsPSDSOSConvex (-(Patx P x))) (v : Fin m → ℝ) (a b : Fin ℓ → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * cval P x v a + (1 - t) * cval P x v b ≤ cval P x v (t • a + (1 - t) • b) := by
  have H := evalP_concave P hP x hc a b t ht0 ht1
  have hq := (posSemidef_iff_dotProduct_mulVec.1 H).2 v
  rw [quad_eq] at hq
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hq
  unfold cval
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  refine le_of_le_of_eq hq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma cval_nonneg (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (y : Fin ℓ → ℝ) (h : (evalP P y x).PosSemidef) (v : Fin m → ℝ) :
    0 ≤ cval P x v y := by
  have := (posSemidef_iff_dotProduct_mulVec.1 h).2 v
  rwa [quad_eq] at this

lemma cval_pos (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (y : Fin ℓ → ℝ) (h : (evalP P y x).PosDef) (v : Fin m → ℝ) (hv : v ≠ 0) :
    0 < cval P x v y := by
  have := (posDef_iff_dotProduct_mulVec.1 h).2 hv
  rwa [quad_eq] at this

lemma cval_smul (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (y : Fin ℓ → ℝ) (c : ℝ) (v : Fin m → ℝ) :
    cval P x (c • v) y = c ^ 2 * cval P x v y := by
  unfold cval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma psd_of_cval (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) (hP : P.IsSymm)
    (x : Fin n → ℝ) (y : Fin ℓ → ℝ)
    (h : ∀ v : Fin m → ℝ, ‖v‖ = 1 → 0 ≤ cval P x v y) : (evalP P y x).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨evalP_isHermitian P hP y x, fun w => ?_⟩
  rw [quad_eq]
  by_cases hw : w = 0
  · subst hw; simp
  · have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have h1 : ‖(‖w‖⁻¹) • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
    have h2 := h _ h1
    rw [cval_smul] at h2
    have h3 : 0 < (‖w‖⁻¹) ^ 2 := by positivity
    have := nonneg_of_mul_nonneg_right (by linarith) h3
    exact this

lemma cval_cont_y (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (x : Fin n → ℝ) (v : Fin m → ℝ) : Continuous fun y => cval P x v y := by
  unfold cval evalP
  simp only [map_apply]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (continuous_const.mul (continuous_eval_elim _ x)).mul continuous_const

lemma cval_cont_xv (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (y : Fin ℓ → ℝ) :
    Continuous fun τ : (Fin n → ℝ) × (Fin m → ℝ) => cval P τ.1 τ.2 y := by
  unfold cval evalP
  simp only [map_apply]
  have hx : ∀ p : MvPolynomial (Fin ℓ ⊕ Fin n) ℝ,
      Continuous fun τ : (Fin n → ℝ) × (Fin m → ℝ) => eval (Sum.elim y τ.1) p := fun p => by
    refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
    rcases i with j | j
    · exact continuous_const
    · exact (continuous_apply j).comp continuous_fst
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    (((continuous_apply a).comp continuous_snd).mul (hx _)).mul
      ((continuous_apply b).comp continuous_snd)

end Cval

section Main
variable {ℓ n m q s : ℕ}
open Filter Topology

lemma Yset_convex (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (hθ : ∀ j, IsSOSConvex (-θ j))
    (a b : Fin ℓ → ℝ) (ha : a ∈ Yset θ) (hb : b ∈ Yset θ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • a + (1 - t) • b ∈ Yset θ := fun j => by
  have := jensen2_scalar (-θ j) (hθ j) a b t ht0 ht1
  simp only [map_neg] at this
  have := ha j; have := hb j
  nlinarith

lemma Yset_closed (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) : IsClosed (Yset θ) := by
  have : Yset θ = ⋂ j, {y | 0 ≤ eval y (θ j)} := by ext y; simp [Yset]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le continuous_const (MvPolynomial.continuous_eval _)

/-- The core of Proposition 4.1: finitely many multipliers `λᵢ ≥ 0` at points `(xᵢ, vᵢ)`. -/
lemma finite_multipliers (f : MvPolynomial (Fin ℓ) ℝ) (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ)) (hP : P.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G) (ys : Fin ℓ → ℝ)
    (hys : IsGlobalMin f θ P G ys) :
    ∃ (k : ℕ) (xs : Fin k → Fin n → ℝ) (vs : Fin k → Fin m → ℝ) (lam : Fin k → ℝ),
      (∀ i, xs i ∈ Xset G) ∧ (∀ i, 0 ≤ lam i) ∧
      ∀ y ∈ Yset θ, eval ys f ≤ eval y f - ∑ i, lam i * cval P (xs i) (vs i) y := by
  classical
  obtain ⟨hf, hθ, hPc, hXc⟩ := h1
  obtain ⟨yb, hybY, hybθ, hybP⟩ := h3
  set fs := eval ys f
  set Tset : Set ((Fin n → ℝ) × (Fin m → ℝ)) := Xset G ×ˢ Metric.sphere (0 : Fin m → ℝ) 1
  have hTc : IsCompact Tset := hXc.prod (isCompact_sphere _ _)
  have hfeas : ∀ y ∈ Yset θ, (∀ τ ∈ Tset, 0 ≤ cval P τ.1 τ.2 y) → fs ≤ eval y f := by
    intro y hy hc
    refine hys.2 y ⟨hy, fun x hx => psd_of_cval P hP x y fun v hv => hc (x, v) ⟨hx, ?_⟩⟩
    simpa using hv
  by_cases hTe : Tset = ∅
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun y hy => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact hfeas y hy fun τ hτ => by rw [hTe] at hτ; exact hτ.elim
  have hTne : Tset.Nonempty := Set.nonempty_iff_ne_empty.2 hTe
  -- uniform Slater constant
  obtain ⟨τm, hτmT, hτm⟩ := hTc.exists_isMinOn hTne (cval_cont_xv P yb).continuousOn
  set δ := cval P τm.1 τm.2 yb
  have hδ : 0 < δ := cval_pos P _ yb (hybP _ hτmT.1) _ (by
    intro h0; have := hτmT.2; rw [h0] at this; simp at this)
  have hδle : ∀ τ ∈ Tset, δ ≤ cval P τ.1 τ.2 yb := fun τ hτ => hτm hτ
  have hybF : yb ∈ Feasible θ P G := ⟨hybY, fun x hx => (hybP x hx).posSemidef⟩
  have hfyb : fs ≤ eval yb f := hys.2 yb hybF
  set Λ := (eval yb f - fs + 1) / δ
  -- the compact convex set `Z`
  set R := dist yb ys + 1
  set Z := Yset θ ∩ Metric.closedBall ys R
  have hZc : IsCompact Z := (isCompact_closedBall ys R).inter_left (Yset_closed θ)
  have hZconv : ∀ a ∈ Z, ∀ b ∈ Z, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • a + (1 - t) • b ∈ Z := by
    intro a ha b hb t ht0 ht1
    refine ⟨Yset_convex θ hθ a b ha.1 hb.1 t ht0 ht1, ?_⟩
    exact (convex_closedBall ys R) ha.2 hb.2 ht0 (by linarith : (0 : ℝ) ≤ 1 - t)
      (by ring : t + (1 - t) = 1)
  have hybZ : yb ∈ Z := ⟨hybY, by simp [R, Metric.mem_closedBall]⟩
  -- one `ε`-step: Helly + finite Lagrange duality
  have step : ∀ N : ℕ, ∃ (τ : Fin (ℓ + 1) → (Fin n → ℝ) × (Fin m → ℝ)) (lam : Fin (ℓ + 1) → ℝ),
      (∀ k, τ k ∈ Tset) ∧ (∀ k, lam k ∈ Set.Icc 0 Λ) ∧
      ∀ y ∈ Z, fs - 1 / ((N : ℝ) + 1) ≤ eval y f - ∑ k, lam k * cval P (τ k).1 (τ k).2 y := by
    intro N
    set ε : ℝ := 1 / ((N : ℝ) + 1)
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    set F : Tset → Set (Fin ℓ → ℝ) := fun τ =>
      {y | y ∈ Z ∧ 0 ≤ cval P τ.1.1 τ.1.2 y ∧ eval y f ≤ fs - ε}
    have hFconv : ∀ τ, Convex ℝ (F τ) := by
      intro τ y1 hy1 y2 hy2 a b ha hb hab
      have hb' : b = 1 - a := by linarith
      subst hb'
      refine ⟨hZconv y1 hy1.1 y2 hy2.1 a ha (by linarith), ?_, ?_⟩
      · have := cval_concave P hP τ.1.1 (hPc _ τ.2.1) τ.1.2 y1 y2 a ha (by linarith)
        nlinarith [hy1.2.1, hy2.2.1]
      · have := jensen2_scalar f hf y1 y2 a ha (by linarith)
        nlinarith [hy1.2.2, hy2.2.2]
    have hFcomp : ∀ τ, IsCompact (F τ) := by
      intro τ
      have : F τ = Z ∩ ({y | 0 ≤ cval P τ.1.1 τ.1.2 y} ∩ {y | eval y f ≤ fs - ε}) := by
        ext y; exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
      rw [this]
      exact hZc.inter_right ((isClosed_le continuous_const (cval_cont_y P _ _)).inter
        (isClosed_le (MvPolynomial.continuous_eval f) continuous_const))
    have hempty : ¬ (⋂ τ, F τ).Nonempty := by
      rintro ⟨y, hy⟩
      rw [Set.mem_iInter] at hy
      have hyZ : y ∈ Z := (hy ⟨τm, hτmT⟩).1
      have := hfeas y hyZ.1 fun τ hτ => (hy ⟨τ, hτ⟩).2.1
      have := (hy ⟨τm, hτmT⟩).2.2
      linarith
    have hI : ∃ I : Finset Tset, I.card ≤ ℓ + 1 ∧ ¬ (⋂ τ ∈ I, F τ).Nonempty := by
      by_contra hcon
      push Not at hcon
      apply hempty
      refine Convex.helly_theorem_compact' (𝕜 := ℝ) hFconv hFcomp fun I hI => ?_
      rw [Module.finrank_fin_fun] at hI
      exact hcon I hI
    obtain ⟨I, hIcard, hIempty⟩ := hI
    have hIne : I.Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty] at h0
      subst h0
      exact hIempty ⟨yb, by simp⟩
    obtain ⟨τ0, hτ0⟩ := hIne
    -- pad `I` to a family indexed by `Fin (ℓ + 1)`
    set τf : Fin (ℓ + 1) → Tset := fun k =>
      if h : (k : ℕ) < I.card then (I.equivFin.symm ⟨k, h⟩).1 else τ0
    have hτfI : ∀ k, τf k ∈ I := fun k => by
      simp only [τf]; split_ifs
      · exact (I.equivFin.symm _).2
      · exact hτ0
    have hIτf : ∀ τ ∈ I, ∃ k, τf k = τ := fun τ hτ => by
      set e := I.equivFin ⟨τ, hτ⟩
      refine ⟨⟨e, by have := e.2; omega⟩, ?_⟩
      simp only [τf, dif_pos e.2]
      simp [e]
    have hmin' : ∀ y ∈ Z, (∀ k, 0 ≤ cval P (τf k).1.1 (τf k).1.2 y) → fs - ε ≤ eval y f := by
      intro y hyZ hc
      by_contra hlt
      push Not at hlt
      apply hIempty
      refine ⟨y, Set.mem_iInter₂.2 fun τ hτ => ?_⟩
      obtain ⟨k, hk⟩ := hIτf τ hτ
      exact ⟨hyZ, hk ▸ hc k, hlt.le⟩
    obtain ⟨lam, hlam0, hlam⟩ := lagrange_gen Z hZconv (fun y => eval y f)
      (fun a ha b hb t ht0 ht1 => jensen2_scalar f hf a b t ht0 ht1)
      (fun k y => cval P (τf k).1.1 (τf k).1.2 y)
      (fun k a ha b hb t ht0 ht1 => cval_concave P hP _ (hPc _ (τf k).2.1) _ a b t ht0 ht1)
      yb hybZ (fun k => lt_of_lt_of_le hδ (hδle _ (τf k).2)) (fs - ε) hmin'
    refine ⟨fun k => (τf k).1, lam, fun k => (τf k).2, fun k => ⟨hlam0 k, ?_⟩, fun y hy => ?_⟩
    · have hb := hlam yb hybZ
      have hsum : lam k * δ ≤ ∑ k, lam k * cval P (τf k).1.1 (τf k).1.2 yb := by
        refine le_trans (mul_le_mul_of_nonneg_left (hδle _ (τf k).2) (hlam0 k)) ?_
        exact Finset.single_le_sum (f := fun k => lam k * cval P (τf k).1.1 (τf k).1.2 yb)
          (fun j _ => mul_nonneg (hlam0 j) (cval_nonneg P _ yb (hybP _ (τf j).2.1).posSemidef _))
          (Finset.mem_univ k)
      simp only [Λ]
      rw [le_div_iff₀ hδ]
      linarith
    · have := hlam y hy
      linarith
  choose τs lams hτs hlams hstep using step
  -- compactness and a convergent subsequence
  set Kset : Set ((Fin (ℓ + 1) → (Fin n → ℝ) × (Fin m → ℝ)) × (Fin (ℓ + 1) → ℝ)) :=
    (Set.univ.pi fun _ => Tset) ×ˢ (Set.univ.pi fun _ => Set.Icc 0 Λ)
  have hKc : IsCompact Kset :=
    (isCompact_univ_pi fun _ => hTc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hmemK : ∀ N, (τs N, lams N) ∈ Kset := fun N =>
    ⟨fun k _ => hτs N k, fun k _ => hlams N k⟩
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmemK
  have hgcont : ∀ y, Continuous fun p : (Fin (ℓ + 1) → (Fin n → ℝ) × (Fin m → ℝ)) ×
      (Fin (ℓ + 1) → ℝ) => eval y f - ∑ k, p.2 k * cval P (p.1 k).1 (p.1 k).2 y := fun y =>
    continuous_const.sub (continuous_finsetSum _ fun k _ =>
      ((continuous_apply k).comp continuous_snd).mul
        ((cval_cont_xv P y).comp ((continuous_apply k).comp continuous_fst)))
  have hZbound : ∀ y ∈ Z, fs ≤ eval y f - ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 y := by
    intro y hy
    have hL : Tendsto (fun N => fs - 1 / ((φ N : ℝ) + 1)) atTop (𝓝 fs) := by
      have h2 : Tendsto (fun N => 1 / ((φ N : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := fs)).sub h2
    have hR := ((hgcont y).tendsto a).comp hlim
    exact le_of_tendsto_of_tendsto' hL hR fun N => hstep (φ N) y hy
  -- extend from `Z` to `𝒴` by convexity
  have haT : ∀ k, a.1 k ∈ Tset := fun k => haK.1 k (Set.mem_univ _)
  have ha0 : ∀ k, 0 ≤ a.2 k := fun k => (haK.2 k (Set.mem_univ _)).1
  set Lf : (Fin ℓ → ℝ) → ℝ := fun y => eval y f - ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 y
  have hLconv : ∀ y1 y2 : Fin ℓ → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Lf (t • y1 + (1 - t) • y2) ≤ t * Lf y1 + (1 - t) * Lf y2 := by
    intro y1 y2 t ht0 ht1
    have J := jensen2_scalar f hf y1 y2 t ht0 ht1
    have C : ∀ k, t * cval P (a.1 k).1 (a.1 k).2 y1 + (1 - t) * cval P (a.1 k).1 (a.1 k).2 y2 ≤
        cval P (a.1 k).1 (a.1 k).2 (t • y1 + (1 - t) • y2) := fun k =>
      cval_concave P hP _ (hPc _ (haT k).1) _ y1 y2 t ht0 ht1
    have hsum : t * ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 y1 +
        (1 - t) * ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 y2 ≤
        ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 (t • y1 + (1 - t) • y2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => by nlinarith [C k, ha0 k]
    simp only [Lf]
    linarith
  have hLys : Lf ys ≤ fs := by
    have : 0 ≤ ∑ k, a.2 k * cval P (a.1 k).1 (a.1 k).2 ys := Finset.sum_nonneg fun k _ =>
      mul_nonneg (ha0 k) (cval_nonneg P _ ys (hys.1.2 _ (haT k).1) _)
    simp only [Lf]; linarith
  refine ⟨ℓ + 1, fun k => (a.1 k).1, fun k => (a.1 k).2, a.2, fun k => (haT k).1, ha0,
    fun y hy => ?_⟩
  show fs ≤ Lf y
  by_cases hyZ : y ∈ Z
  · exact hZbound y hyZ
  · have hd : R < dist y ys := by
      by_contra h; push Not at h
      exact hyZ ⟨hy, Metric.mem_closedBall.2 h⟩
    have hdpos : 0 < dist y ys := lt_of_le_of_lt (by positivity) hd
    set t := R / dist y ys
    have ht0 : 0 < t := div_pos (by positivity) hdpos
    have ht1 : t ≤ 1 := (div_le_one hdpos).2 hd.le
    have hzY : t • y + (1 - t) • ys ∈ Yset θ := Yset_convex θ hθ y ys hy hys.1.1 t ht0.le ht1
    have hzB : t • y + (1 - t) • ys ∈ Metric.closedBall ys R := by
      rw [Metric.mem_closedBall, dist_eq_norm,
        show t • y + (1 - t) • ys - ys = t • (y - ys) by rw [sub_smul, one_smul, smul_sub]; abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm]
      simp only [t]; rw [div_mul_cancel₀ _ hdpos.ne']
    have hz := hZbound _ ⟨hzY, hzB⟩
    have hc := hLconv y ys t ht0.le ht1
    change fs ≤ Lf (t • y + (1 - t) • ys) at hz
    nlinarith

end Main

end RobustPMI.Hierarchy.P41aux

namespace RobustPMI.Hierarchy.P41aux
open MvPolynomial Matrix RobustPMI.Hierarchy

/-- Merge finitely many weighted rank-one atoms into an `AtomicMeasure` (distinct points). -/
lemma exists_atomic {ℓ n m q : ℕ} (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ)) {k : ℕ}
    (xs : Fin k → Fin n → ℝ) (vs : Fin k → Fin m → ℝ) (lam : Fin k → ℝ)
    (hxs : ∀ i, xs i ∈ Xset G) (hlam : ∀ i, 0 ≤ lam i) :
    ∃ μ : AtomicMeasure m G, ∀ y, μ.rieszP P y = ∑ i, lam i * cval P (xs i) (vs i) y := by
  classical
  set S : Finset (Fin n → ℝ) := Finset.univ.image xs
  set e := S.equivFin
  have hmemS : ∀ i, xs i ∈ S := fun i => Finset.mem_image_of_mem xs (Finset.mem_univ i)
  set g : Fin k → Fin S.card := fun i => e ⟨xs i, hmemS i⟩
  have hg : ∀ i, (e.symm (g i)).1 = xs i := fun i => by simp [g]
  refine ⟨⟨S.card, fun j => (e.symm j).1,
    fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), lam i • vecMulVec (vs i) (vs i),
    fun j1 j2 h => e.symm.injective (Subtype.ext h), fun j => ?_, fun j => ?_⟩, fun y => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (e.symm j).2
    rw [← hi]; exact hxs i
  · refine posSemidef_sum _ fun i _ => ?_
    have := posSemidef_vecMulVec_self_star (vs i)
    rw [star_trivial] at this
    exact this.smul (hlam i)
  · simp only [AtomicMeasure.rieszP]
    rw [← Finset.sum_fiberwise Finset.univ g]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_sum, trace_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : g i = j := (Finset.mem_filter.1 hi).2
    have hx : (e.symm j).1 = xs i := by rw [← hij, hg]
    rw [hx, mul_smul_comm, trace_smul, smul_eq_mul]
    congr 1
    simp only [trace, diag, mul_apply, vecMulVec_apply, cval]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end RobustPMI.Hierarchy.P41aux

open RobustPMI.Hierarchy RobustPMI.Hierarchy.P41aux MvPolynomial Matrix in
theorem solution {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    ∃ μ : AtomicMeasure m G,
      IsGLB ((fun y => eval y f - μ.rieszP P y) '' Yset θ) (fstar f θ P G) ∧
      ∀ y, IsGlobalMin f θ P G y → μ.rieszP P y = 0 := by
  obtain ⟨ys, hys⟩ := hmin
  obtain ⟨k, xs, vs, lam, hxs, hlam, hbound⟩ := finite_multipliers f θ P G hP h1 h3 ys hys
  obtain ⟨μ, hμ⟩ := exists_atomic G P xs vs lam hxs hlam
  have hfs := fstar_eq f θ P G ys hys
  have hRnn : ∀ y ∈ Feasible θ P G, 0 ≤ μ.rieszP P y := fun y hy => by
    rw [hμ]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (cval_nonneg P _ y (hy.2 _ (hxs i)) _)
  have hzero : ∀ y, IsGlobalMin f θ P G y → μ.rieszP P y = 0 := by
    intro y hy
    have hfy : eval y f = eval ys f := by
      rw [← fstar_eq f θ P G y hy, hfs]
    have hb := hbound y hy.1.1
    rw [← hμ, hfy] at hb
    have := hRnn y hy.1
    linarith
  refine ⟨μ, ⟨?_, fun b hb => ?_⟩, hzero⟩
  · rintro _ ⟨y, hy, rfl⟩
    have := hbound y hy
    rw [← hμ] at this
    simp only
    rw [hfs]; exact this
  · have := hb ⟨ys, hys.1.1, rfl⟩
    simp only [hzero ys hys, sub_zero] at this
    rw [hfs]; exact this
