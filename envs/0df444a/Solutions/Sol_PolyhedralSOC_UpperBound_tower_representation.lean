-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.tower_representation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:59:13.770145+00:00
-- url     : https://prove2.me/submissions/93b62dd1-9a27-4850-8847-2511531b4cc7

import Definitions.Def_PolyhedralSOC_UpperBound_Tower
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

namespace SOCTower
open Finset PolyhedralSOC PolyhedralSOC.UpperBound

lemma sum_pairs (f:ℕ→ℝ) (n:ℕ) :
    ∑i∈range (2*n),f i=∑i∈range n,(f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring

noncomputable def foldNorm (f:ℕ→ℝ) : ℕ→ℕ→ℝ
  | 0=>f
  | n+1=>fun i=>Real.sqrt (foldNorm f n (2*i)^2+foldNorm f n (2*i+1)^2)

lemma fold_nonneg (f:ℕ→ℝ) (n:ℕ) (hn:1≤n) (i:ℕ) : 0≤foldNorm f n i := by
  cases n with
  | zero => omega
  | succ n => exact Real.sqrt_nonneg _

lemma fold_energy (f:ℕ→ℝ) (θ l:ℕ) (hl:l≤θ) :
    ∑i∈range (2^(θ-l)),foldNorm f l i^2=∑i∈range (2^θ),f i^2 := by
  induction l with
  | zero => simp [foldNorm]
  | succ l ih =>
    have hp : 2^(θ-l)=2*2^(θ-(l+1)) := by
      rw [show θ-l=(θ-(l+1))+1 by omega,pow_succ]
      omega
    have hsum : ∑i∈range (2^(θ-(l+1))),foldNorm f (l+1) i^2=
        ∑i∈range (2^(θ-l)),foldNorm f l i^2 := by
      rw [hp,sum_pairs]
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.sq_sqrt (by positivity)
    exact hsum.trans (ih (by omega))

lemma fold_top (f:ℕ→ℝ) (θ:ℕ) (hθ:1≤θ) :
    foldNorm f θ 0=Real.sqrt (∑i∈range (2^θ),f i^2) := by
  have he := fold_energy f θ θ le_rfl
  simp only [Nat.sub_self,pow_zero,sum_range_one] at he
  rw [←he,Real.sqrt_sq (fold_nonneg f θ hθ 0)]

lemma exists_tower (θ:ℕ) (hθ:1≤θ) (y:Fin (2^θ)→ℝ) (t:ℝ) (hy:Shared.eucNorm y≤t) :
    ∃Y,IsTowerOf θ y t Y ∧ TowerSystem5 θ Y := by
  classical
  let f : ℕ→ℝ := fun i=>if h:i<2^θ then y ⟨i,h⟩ else 0
  have hf (i:Fin (2^θ)) : f i=y i := by simp [f]
  have he : Real.sqrt (∑i∈range (2^θ),f i^2)=Shared.eucNorm y := by
    unfold Shared.eucNorm
    rw [←Fin.sum_univ_eq_sum_range]
    congr 1
    exact Finset.sum_congr rfl (fun i _=>by rw [hf])
  let Y : ℕ→ℕ→ℝ := fun l i=>if l<θ then foldNorm f l i else t
  refine ⟨Y,⟨?_,?_⟩,?_⟩
  · intro i;simp [Y,show 0<θ by omega,foldNorm,hf]
  · simp [Y]
  · intro l hl hlθ i hi
    have hlp : l-1<θ := by omega
    have heq : l-1+1=l := by omega
    have hfrec : Real.sqrt (foldNorm f (l-1) (2*i)^2+foldNorm f (l-1) (2*i+1)^2)=foldNorm f l i := by
      rw [←heq];rfl
    simp only [Y,if_pos hlp]
    rw [hfrec]
    by_cases hlt:l<θ
    · simp [hlt]
    · have hlθ':l=θ := by omega
      subst l
      have hi0:i=0 := by simpa using hi
      subst i
      simp only [lt_self_iff_false,if_false]
      rw [fold_top f θ hθ,he]
      exact hy

noncomputable def levelNorm (θ l:ℕ) (Y:ℕ→ℕ→ℝ) : ℝ :=
  Real.sqrt (∑i∈range (2^(θ-l)),Y l i^2)

lemma level_step (θ l:ℕ) (hl:1≤l) (hlθ:l≤θ) (Y:ℕ→ℕ→ℝ) (a:ℝ) (ha:0≤a)
    (h:∀i<2^(θ-l),Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)≤a*Y l i) :
    levelNorm θ (l-1) Y≤a*levelNorm θ l Y := by
  have hp : 2^(θ-(l-1))=2*2^(θ-l) := by
    rw [show θ-(l-1)=(θ-l)+1 by omega,pow_succ]
    omega
  have hs : ∑i∈range (2^(θ-(l-1))),Y (l-1) i^2≤a^2*(∑i∈range (2^(θ-l)),Y l i^2) := by
    rw [hp,sum_pairs,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh := h i (Finset.mem_range.mp hi)
    have hn := Real.sqrt_nonneg (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)
    have he := Real.sq_sqrt (show 0≤Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2 by positivity)
    nlinarith [sq_nonneg (a*Y l i-Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2))]
  unfold levelNorm
  have he := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha] at he
  exact he

lemma quality (θ:ℕ) (hθ:1≤θ) (y:Fin (2^θ)→ℝ) (t:ℝ) (Y:ℕ→ℕ→ℝ)
    (hY:IsTowerOf θ y t Y) (a:ℕ→ℝ) (ha:∀l,1≤l → l≤θ → 0<a l)
    (h:∀l,1≤l → l≤θ → ∀i<2^(θ-l),
      Real.sqrt (Y (l-1) (2*i)^2+Y (l-1) (2*i+1)^2)≤a l*Y l i) :
    Shared.eucNorm y≤(∏l∈Icc 1 θ,a l)*t := by
  have hn (l:ℕ) : 0≤levelNorm θ l Y := Real.sqrt_nonneg _
  have hp (l:ℕ) (hl:l≤θ) : 0≤∏j∈Icc 1 l,a j :=
    Finset.prod_nonneg (fun j hj=>(ha j (Finset.mem_Icc.mp hj).1 ((Finset.mem_Icc.mp hj).2.trans hl)).le)
  have hind (l:ℕ) (hl:l≤θ) : levelNorm θ 0 Y≤(∏j∈Icc 1 l,a j)*levelNorm θ l Y := by
    induction l with
    | zero => simp
    | succ l ih =>
      have hi := ih (by omega)
      have hs := level_step θ (l+1) (by omega) hl Y (a (l+1)) (ha (l+1) (by omega) hl).le (h (l+1) (by omega) hl)
      simp only [Nat.add_sub_cancel] at hs
      have hh := mul_le_mul_of_nonneg_left hs (hp l (by omega))
      rw [Finset.prod_Icc_succ_top (by omega)]
      nlinarith
  have hbase : levelNorm θ 0 Y=Shared.eucNorm y := by
    unfold levelNorm Shared.eucNorm
    rw [Nat.sub_zero,←Fin.sum_univ_eq_sum_range]
    congr 1
    exact Finset.sum_congr rfl (fun i _=>by rw [hY.1 i])
  have ht : 0≤t := by
    have hh := h θ hθ le_rfl 0 (by simp)
    rw [hY.2] at hh
    have hpθ := ha θ hθ le_rfl
    nlinarith [Real.sqrt_nonneg (Y (θ-1) 0^2+Y (θ-1) 1^2)]
  have htop : levelNorm θ θ Y=t := by simp [levelNorm,hY.2,Real.sqrt_sq ht]
  simpa [hbase,htop] using hind θ le_rfl

end SOCTower

namespace SOCTower
open Finset PolyhedralSOC PolyhedralSOC.UpperBound

lemma composition (θ:ℕ) (hθ:1≤θ) (p q:ℕ→ℕ) (ε:ℕ→ℝ)
    (Ps:(l:ℕ)→(Fin 2→ℝ)×ℝ×(Fin (p l)→ℝ)→ₗ[ℝ](Fin (q l)→ℝ))
    (hε:∀l,1≤l → l≤θ → 0<ε l)
    (hP:∀l,1≤l → l≤θ → Shared.IsPolyhedralApprox 2 (p l) (q l) (ε l) (Ps l)) :
    (∀ (y:Fin (2^θ)→ℝ) (t:ℝ),(y,t)∈Shared.LorentzCone (2^θ) →
      ∃ (Y:ℕ→ℕ→ℝ) (U:(l:ℕ)→ℕ→Fin (p l)→ℝ),IsTowerOf θ y t Y ∧ TowerSystem6 θ p q Ps Y U) ∧
    (∀ (y:Fin (2^θ)→ℝ) (t:ℝ) (Y:ℕ→ℕ→ℝ) (U:(l:ℕ)→ℕ→Fin (p l)→ℝ),
      IsTowerOf θ y t Y → TowerSystem6 θ p q Ps Y U →
        Shared.eucNorm y≤(∏l∈Icc 1 θ,(1+ε l))*t) := by
  classical
  constructor
  · intro y t hy
    obtain ⟨Y,hY,h5⟩ := exists_tower θ hθ y t hy
    have hex : ∀l i:ℕ,∃u:Fin (p l)→ℝ,1≤l → l≤θ → i<2^(θ-l) →
        0≤Ps l (![Y (l-1) (2*i),Y (l-1) (2*i+1)],Y l i,u) := by
      intro l i
      by_cases h:1≤l ∧ l≤θ ∧ i<2^(θ-l)
      · have hh : (![Y (l-1) (2*i),Y (l-1) (2*i+1)],Y l i)∈Shared.LorentzCone 2 := by
          simpa [Shared.LorentzCone,Shared.eucNorm,Fin.sum_univ_two] using h5 l h.1 h.2.1 i h.2.2
        obtain ⟨u,hu⟩ := (hP l h.1 h.2.1).1 _ _ hh
        exact ⟨u,fun _ _ _=>hu⟩
      · exact ⟨0,fun h1 h2 h3=>False.elim (h ⟨h1,h2,h3⟩)⟩
    choose U hU using hex
    exact ⟨Y,U,hY,fun l h1 h2 i hi=>hU l i h1 h2 hi⟩
  · intro y t Y U hY h6
    apply quality θ hθ y t Y hY (fun l=>1+ε l) (fun l h1 h2=>by linarith [hε l h1 h2])
    intro l h1 h2 i hi
    have hh := (hP l h1 h2).2 _ (Y l i) (U l i) (h6 l h1 h2 i hi)
    simpa [Shared.eucNorm,Fin.sum_univ_two] using hh

end SOCTower

namespace PolyhedralSOC.UpperBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), §2, Eq. (5), p. 199 (PDF p. 7): for `k = 2^θ`,
`θ ≥ 1`, a pair `(y, t)` can be extended to a tower `Y` solving (5) if and only if
`(y, t)` solves (CQI) `√(y_1² + ⋯ + y_k²) ≤ t`. -/
theorem _root_.solution (θ : ℕ) (hθ : 1 ≤ θ) (y : Fin (2 ^ θ) → ℝ) (t : ℝ) :
    (∃ Y : ℕ → ℕ → ℝ, IsTowerOf θ y t Y ∧ TowerSystem5 θ Y) ↔ Shared.eucNorm y ≤ t := by
  constructor
  · rintro ⟨Y,hY,h5⟩
    simpa using SOCTower.quality θ hθ y t Y hY (fun _=>1) (by intros;norm_num)
      (by simpa [TowerSystem5] using h5)
  · exact SOCTower.exists_tower θ hθ y t

end PolyhedralSOC.UpperBound
