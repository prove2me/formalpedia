-- Prove2me | solution 1 for QSVT19.Main.corollary_18
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T04:50:00.825467+00:00
-- url     : https://prove2.me/submissions/705d04a7-660c-4078-bd64-b03557a0ca1c

import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_QSVT19_Main_corollary_8
import Theorems.Thm_QSVT19_Main_corollary_10
import Theorems.Thm_QSVT19_Main_theorem_17

noncomputable section
open Polynomial Matrix QAlgorithms QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTMain
lemma poly_conj_eval (P : ℂ[X]) (x : ℝ) : (P.map (starRingEnd ℂ)).eval (x:ℂ)=conj (P.eval (x:ℂ)) := by
  simpa only [Polynomial.eval_map,Complex.conj_ofReal] using (Polynomial.eval₂_at_apply (p:=P) (starRingEnd ℂ) (x:ℂ))
lemma Z_conj (a : ℝ) : (qspZ a).map (starRingEnd ℂ) = qspZ (-a) := by
  ext i j;fin_cases i <;>fin_cases j <;>simp [qspZ,← Complex.exp_conj]
lemma R_conj (x : ℝ) : (reflR x).map (starRingEnd ℂ) = reflR x := by
  ext i j;fin_cases i <;>fin_cases j <;>simp [reflR]
lemma qsp_neg {n : ℕ} (Φ : Fin n → ℝ) (x : ℝ) :
    qspRefl (-Φ) x = (qspRefl Φ x).map (starRingEnd ℂ) := by
  unfold qspRefl
  change _ = (starRingEnd ℂ).mapMatrix _
  rw [map_list_prod]
  rw [List.map_ofFn]
  congr 2
  funext j
  change qspZ (-Φ j)*reflR x = (qspZ (Φ j)*reflR x).map (starRingEnd ℂ)
  rw [Matrix.map_mul,Z_conj,R_conj]
lemma eval_real (p : ℝ[X]) (x : ℝ) : (p.map Complex.ofRealHom).eval (x:ℂ) = ((p.eval x:ℝ):ℂ) := by
  rw [eval_map]
  exact Polynomial.eval₂_at_apply (p:=p) Complex.ofRealHom x
lemma real_average (P : ℂ[X]) (PR : ℝ[X]) (h : RePartEq P PR) (x : ℝ) :
    P.eval (x:ℂ) + (P.map (starRingEnd ℂ)).eval (x:ℂ) = (2:ℂ)*(PR.eval x:ℝ) := by
  have he : P+P.map (starRingEnd ℂ) = C 2 * PR.map Complex.ofRealHom := by
    ext i
    simp only [coeff_add,coeff_map,coeff_C_mul]
    rw [← h i]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  have hh := congrArg (Polynomial.eval (x:ℂ)) he
  simpa only [eval_add,eval_mul,eval_C,eval_real] using hh
lemma plus_average {ι : Type*} [Fintype ι] [DecidableEq ι] (A B V W : Matrix ι ι ℂ) :
    plusBra A * ctrlSel V W * plusKet B = (2:ℂ)⁻¹ • (A*V*B+A*W*B) := by
  have hs : (Real.sqrt 2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast hs
  have hz : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  have hcoef : ((Real.sqrt 2:ℂ)⁻¹)^2 = (2:ℂ)⁻¹ := by rw [inv_pow,hc]
  ext i j
  simp only [plusBra,plusKet,ctrlSel,Matrix.mul_apply,Matrix.of_apply,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Fintype.sum_prod_type,Fin.sum_univ_two,
    Matrix.kroneckerMap_apply,Matrix.single_apply]
  simp only [and_self,and_true,and_false,ite_true,ite_false,Fin.zero_ne_one,one_ne_zero,one_mul,zero_mul,add_zero,zero_add]
  rw [mul_add]
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ((Real.sqrt 2:ℂ)⁻¹)^2 * (A i b*V b a*B a j + A i b*W b a*B a j) := by ring
    _ = _ := by rw [hcoef];ring
end QSVTMain

noncomputable section
open Polynomial Matrix QAlgorithms QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTMain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma qsp_conjugate {n : ℕ} (Φ : Fin n → ℝ) (P : ℂ[X])
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, qspRefl Φ x 0 0=P.eval (x:ℂ)) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1, qspRefl (-Φ) x 0 0=(P.map (starRingEnd ℂ)).eval (x:ℂ) := by
  intro x hx
  rw [qsp_neg]
  change conj (qspRefl Φ x 0 0) = _
  rw [h x hx,poly_conj_eval]
lemma svt_odd_average {U A B : Matrix ι ι ℂ} (S : ProjUnitarySVD U A B)
    (P : ℂ[X]) (PR : ℝ[X]) (h : RePartEq P PR) :
    svtOdd (fun x => ((PR.eval x:ℝ):ℂ)) S = (2:ℂ)⁻¹ •
      (svtOdd (fun x => P.eval (x:ℂ)) S + svtOdd (fun x => (P.map (starRingEnd ℂ)).eval (x:ℂ)) S) := by
  have hh (x : ℝ) : (2:ℂ)⁻¹*(P.eval (x:ℂ)+(P.map (starRingEnd ℂ)).eval (x:ℂ))=((PR.eval x:ℝ):ℂ) := by
    rw [real_average P PR h];ring
  simp only [svtOdd,Finset.smul_sum,← Finset.sum_add_distrib,← add_smul,smul_smul,hh]
lemma svt_even_average {U A B : Matrix ι ι ℂ} (S : ProjUnitarySVD U A B)
    (P : ℂ[X]) (PR : ℝ[X]) (h : RePartEq P PR) :
    svtEven (fun x => ((PR.eval x:ℝ):ℂ)) S = (2:ℂ)⁻¹ •
      (svtEven (fun x => P.eval (x:ℂ)) S + svtEven (fun x => (P.map (starRingEnd ℂ)).eval (x:ℂ)) S) := by
  have hh (x : ℝ) : (2:ℂ)⁻¹*(P.eval (x:ℂ)+(P.map (starRingEnd ℂ)).eval (x:ℂ))=((PR.eval x:ℝ):ℂ) := by
    rw [real_average P PR h];ring
  simp only [svtEven,Finset.smul_sum,← Finset.sum_add_distrib,← add_smul,smul_smul,hh]
theorem main_checked (U A B : Matrix ι ι ℂ) (hU : U ∈ unitaryGroup ι ℂ)
    (hA : IsStarProjection A) (hB : IsStarProjection B) (n : ℕ) (hn : 1 ≤ n)
    (PR : ℝ[X]) (hd : PR.natDegree=n) (hp : HasParity (PR.map Complex.ofRealHom) n)
    (hb : ∀ x ∈ Set.Icc (-1:ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ Φ : Fin n → ℝ, ∀ S : ProjUnitarySVD U A B,
      (Odd n → svtOdd (fun x => ((PR.eval x:ℝ):ℂ)) S = plusBra B * ctrlSel (altPhaseSeq U A B Φ) (altPhaseSeq U A B (-Φ)) * plusKet A) ∧
      (Even n → svtEven (fun x => ((PR.eval x:ℝ):ℂ)) S = plusBra A * ctrlSel (altPhaseSeq U A B Φ) (altPhaseSeq U A B (-Φ)) * plusKet A) := by
  obtain ⟨P,hr,hP⟩ := corollary_10 n hn PR hd hp hb
  obtain ⟨Φ,hΦ,_⟩ := corollary_8 n hn P hP
  refine ⟨Φ,fun S => ?_⟩
  have ht := theorem_17 U A B hU hA hB n Φ P hΦ S
  have ht' := theorem_17 U A B hU hA hB n (-Φ) (P.map (starRingEnd ℂ)) (qsp_conjugate Φ P hΦ) S
  constructor
  · intro ho
    rw [plus_average,← ht.1 ho,← ht'.1 ho]
    exact svt_odd_average S P PR hr
  · intro he
    rw [plus_average,← ht.2 he,← ht'.2 he]
    exact svt_even_average S P PR hr
end QSVTMain

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 18 (Singular value transformation by real polynomials), p. 19: "Let U, Π, Π̃ be
as in Theorem 17. Suppose that P_ℜ ∈ R[x] is a degree-n polynomial satisfying that
• P_ℜ has parity-(n mod 2) and • for all x ∈ [−1, 1]: |P_ℜ(x)| ≤ 1.
Then there exist Φ ∈ R^n, such that
P_ℜ^{(SV)}(Π̃UΠ) = (⟨+| ⊗ Π̃)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) if n is odd, and
(⟨+| ⊗ Π)(|0⟩⟨0| ⊗ U_Φ + |1⟩⟨1| ⊗ U_{−Φ})(|+⟩ ⊗ Π) if n is even. (33)"

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). "degree-n" is `natDegree = n`; the parity of `P_ℜ` is that of its image in `ℂ[X]`.
`P_ℜ^{(SV)}(Π̃UΠ)` is Definition 16 applied to `x ↦ P_ℜ(x)` over a singular value decomposition
`S` of `Π̃UΠ` (`svtOdd` for odd `n`, `svtEven` for even `n`); the identity is asserted for every
such decomposition, with `Φ` chosen before it (as `P^{(SV)}` does not depend on the
decomposition). `U_Φ` is `altPhaseSeq`, `⟨+| ⊗ M`, `|+⟩ ⊗ M` and `|0⟩⟨0| ⊗ V + |1⟩⟨1| ⊗ W` are
`plusBra`, `plusKet`, `ctrlSel`, with the ancilla qubit as the first tensor factor. The
hypothesis `1 ≤ n` is added: at `n = 0`, `P_ℜ ≡ c` with `c ≠ 1` satisfies the bullets, its
transformation is `cΠ`, while `Φ ∈ R^0` gives `U_Φ = I` and the right-hand side `Π`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (n : ℕ) (hn : 1 ≤ n) (PR : ℝ[X]) (hdeg : PR.natDegree = n) (hpar : QAlgorithms.HasParity (PR.map Complex.ofRealHom) n) (hbd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |PR.eval x| ≤ 1) :
    ∃ Φ : Fin n → ℝ, ∀ S : ProjUnitarySVD U Proj Projt, (Odd n → svtOdd (fun x : ℝ => ((PR.eval x : ℝ) : ℂ)) S = plusBra Projt * ctrlSel (altPhaseSeq U Proj Projt Φ) (altPhaseSeq U Proj Projt (-Φ)) * plusKet Proj) ∧ (Even n → svtEven (fun x : ℝ => ((PR.eval x : ℝ) : ℂ)) S = plusBra Proj * ctrlSel (altPhaseSeq U Proj Projt Φ) (altPhaseSeq U Proj Projt (-Φ)) * plusKet Proj) := by
  exact QSVTMain.main_checked U Proj Projt hU hProj hProjt n hn PR hdeg hpar hbd