-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:17:02.234318+00:00
-- url     : https://prove2.me/submissions/5d3f9602-6ca3-4bac-bc7c-410acf1656ea

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

open Matrix

namespace SaturatedNet.Uniqueness.IrreducibleProof

lemma pow_mulVec_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (p : n → ℝ) (r : ℝ) (h : P *ᵥ p = r • p) (l : ℕ) :
    P ^ l *ᵥ p = r ^ l • p := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul]
    congr 1

lemma nonneg_eigenvector_pos {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p) :
    ∀ i, 0 < p i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  have hjpos : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hj)
  intro i
  by_contra! hi
  have hiz : p i = 0 := le_antisymm hi (hp i)
  obtain ⟨l, _, hl⟩ := hirr i j
  have hsum : 0 < (P ^ l *ᵥ p) i := by
    exact (Finset.sum_pos_iff_of_nonneg
      (fun a _ => mul_nonneg (Matrix.pow_apply_nonneg hP l i a) (hp a))).2
      ⟨j, Finset.mem_univ j, mul_pos hl hjpos⟩
  rw [pow_mulVec_eigen P p r he l] at hsum
  simp [hiz] at hsum

lemma eigenspace_one_dimensional {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (r : ℝ) (p : n → ℝ) (hp : 0 ≤ p) (hp0 : p ≠ 0) (he : P *ᵥ p = r • p)
    (q : n → ℝ) (hq : P *ᵥ q = r • q) : ∃ t : ℝ, q = t • p := by
  classical
  have hpp := nonneg_eigenvector_pos P hP hirr r p hp hp0 he
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    exact hp0 (funext h)
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun j => q j / p j) ⟨j, Finset.mem_univ j⟩
  let t : ℝ := q i / p i
  have hw : 0 ≤ q - t • p := by
    intro a
    change 0 ≤ q a - t * p a
    exact sub_nonneg.mpr ((le_div_iff₀ (hpp a)).mp (hmin a (Finset.mem_univ a)))
  have hwe : P *ᵥ (q - t • p) = r • (q - t • p) := by
    rw [mulVec_sub, mulVec_smul, hq, he, smul_sub, smul_comm t r]
  have hwz : (q - t • p) i = 0 := by
    change q i - (q i / p i) * p i = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hpp i)), sub_self]
  have hz : q - t • p = 0 := by
    by_contra hn
    have hi := nonneg_eigenvector_pos P hP hirr r (q-t•p) hw hn hwe i
    rw [hwz] at hi
    exact (lt_irrefl 0) hi
  exact ⟨t, sub_eq_zero.mp hz⟩

lemma irreducible_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hirr : IsIrreducible P) : IsIrreducible Pᵀ := by
  intro i j
  obtain ⟨l, hl, hpow⟩ := hirr j i
  exact ⟨l, hl, by simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using hpow⟩

end SaturatedNet.Uniqueness.IrreducibleProof

open Matrix

namespace SaturatedNet.Uniqueness.BalanceLinearProof

lemma sat_contract (w a b : ℝ) : |sat w a-sat w b| ≤ |a-b| := by
  calc
    _ ≤ |max a 0-max b 0| := by
      simpa only [sat,sub_self,abs_zero,max_eq_left (abs_nonneg (max a 0-max b 0))] using
        abs_min_sub_min_le_max (max a 0) w (max b 0) w
    _ ≤ _ := abs_max_sub_max_le_abs a b 0

lemma sat_surplus_imp (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) (ha : w<a) : w<b := by
  by_contra hb
  have hb' : b ≤ w := le_of_not_gt hb
  have hsa : sat w a=w := by
    unfold sat
    rw [max_eq_left (by linarith),min_eq_right ha.le]
  have hsb : sat w b=max b 0 := min_eq_left (max_le hb' hw)
  rw [hsa,hsb,abs_of_nonneg (sub_nonneg.mpr (max_le hb' hw)),
    abs_of_nonneg (show 0 ≤ a-b by linarith)] at he
  linarith [le_max_left b 0]

lemma sat_deficit_imp (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) (ha : a<0) : b<0 := by
  by_contra hb
  have hb' : 0 ≤ b := le_of_not_gt hb
  have hsa : sat w a=0 := by simp [sat,max_eq_right ha.le,min_eq_left hw]
  have hsb : sat w b=min b w := by simp [sat,max_eq_left hb']
  rw [hsa,hsb,abs_of_nonpos (show 0-min b w ≤ 0 by linarith [le_min hb' hw]),
    abs_of_nonpos (show a-b ≤ 0 by linarith)] at he
  linarith [min_le_left b w]

end SaturatedNet.Uniqueness.BalanceLinearProof

namespace SaturatedNet.Uniqueness.BalanceLinearProof

lemma inflow_difference {n : Type*} [Fintype n] (P : Matrix n n ℝ) (c x y : n → ℝ) (i : n) :
    inflow P c x i-inflow P c y i=∑ j,(x j-y j)*P j i := by
  unfold inflow
  rw [add_sub_add_right_eq_sub,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (sub_mul _ _ _).symm)

lemma left_subinvariant_eq {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (p : n → ℝ) (hp : ∀ i, 0 < p i)
    (he : P *ᵥ p = p) (d : n → ℝ) (hd : d ≤ Pᵀ *ᵥ d) :
    Pᵀ *ᵥ d = d := by
  have hw (i : n) : p i*d i ≤ p i*(Pᵀ *ᵥ d) i :=
    mul_le_mul_of_nonneg_left (hd i) (hp i).le
  have hs : (∑ i,p i*(Pᵀ *ᵥ d) i) = ∑ i,p i*d i := by
    change (∑ i,p i*(∑ j,P j i*d j)) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j,(P *ᵥ p) j*d j := by
        apply Finset.sum_congr rfl
        intro j _
        change (∑ i,p i*(P j i*d j)) = (∑ i,P j i*p i)*d j
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [he]
  funext i
  have hi := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => hw j)).mp
    hs.symm i (Finset.mem_univ i)
  exact (mul_left_cancel₀ (ne_of_gt (hp i)) hi).symm

lemma sat_exposed (w a b : ℝ) (hw : 0 ≤ w)
    (he : |sat w a-sat w b|=|a-b|) (hne : sat w a ≠ sat w b) :
    0 ≤ a ∧ a ≤ w := by
  constructor
  · by_contra h
    have ha : a < 0 := lt_of_not_ge h
    have hb := sat_deficit_imp w a b hw he ha
    exact hne (by simp [sat,max_eq_right ha.le,max_eq_right hb.le])
  · by_contra h
    have ha : w < a := lt_of_not_ge h
    have hb := sat_surplus_imp w a b hw he ha
    exact hne (by simp [sat,max_eq_left (show 0 ≤ a by linarith),
      max_eq_left (show 0 ≤ b by linarith),min_eq_right ha.le,min_eq_right hb.le])

end SaturatedNet.Uniqueness.BalanceLinearProof

namespace SaturatedNet.Uniqueness.BalanceProof
open BalanceLinearProof

lemma equilibrium_linear_of_nontrivial {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (p : n → ℝ) (hpp : ∀ i, 0 < p i) (hpP : P *ᵥ p = p)
    (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ)
    (hnt : (equilibria P w c).Nontrivial) :
    ∀ x ∈ equilibria P w c, x = x ᵥ* P + c := by
  classical
  intro x hx
  obtain ⟨y,hy,hyx⟩ := hnt.exists_ne x
  let d : n → ℝ := fun i => |x i-y i|
  have hd : 0 ≤ d := fun i => abs_nonneg _
  have hd0 : d ≠ 0 := by
    intro h
    apply hyx
    funext i
    have hi : |x i-y i|=0 := congrFun h i
    exact (sub_eq_zero.mp (abs_eq_zero.mp hi)).symm
  have hcontract (i : n) : d i ≤ |inflow P c x i-inflow P c y i| := by
    change |x i-y i| ≤ _
    rw [hx i,hy i]
    exact sat_contract _ _ _
  have htriangle (i : n) : |inflow P c x i-inflow P c y i| ≤ (Pᵀ *ᵥ d) i := by
    rw [inflow_difference]
    calc
      _ ≤ ∑ j,|(x j-y j)*P j i| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl (fun j _ => by
        dsimp [d]
        rw [abs_mul,abs_of_nonneg (hP j i),mul_comm])
  have hde : Pᵀ *ᵥ d = d := left_subinvariant_eq P p hpp hpP d
    (fun i => (hcontract i).trans (htriangle i))
  have hdpos : ∀ i,0<d i := IrreducibleProof.nonneg_eigenvector_pos Pᵀ
    (fun i j => hP j i) (IrreducibleProof.irreducible_transpose P hirr) 1 d hd hd0
    (by simpa only [one_smul] using hde)
  funext i
  have hi : d i=|inflow P c x i-inflow P c y i| :=
    le_antisymm (hcontract i) (by simpa only [hde] using htriangle i)
  have he : |sat (w i) (inflow P c x i)-sat (w i) (inflow P c y i)| =
      |inflow P c x i-inflow P c y i| := by
    rw [← hx i,← hy i]
    exact hi
  have hne : sat (w i) (inflow P c x i) ≠ sat (w i) (inflow P c y i) := by
    rw [← hx i,← hy i]
    intro h
    have hpos := hdpos i
    change 0 < |x i-y i| at hpos
    simp [h] at hpos
  have hr := sat_exposed (w i) (inflow P c x i) (inflow P c y i) (hw i) he hne
  calc
    x i = sat (w i) (inflow P c x i) := hx i
    _ = inflow P c x i := by simp [sat,max_eq_left hr.1,min_eq_left hr.2]
    _ = (x ᵥ* P+c) i := rfl

end SaturatedNet.Uniqueness.BalanceProof

open Matrix

namespace SaturatedNet.Uniqueness.BalanceProof

lemma le_minRatio_iff {n : Type*} [Fintype n] [Nonempty n]
    (a b : n → ℝ) (r : ℝ) :
    r ≤ minRatio a b Finset.univ_nonempty ↔ ∀ i, r ≤ a i / b i := by
  simp [minRatio]

lemma line_bounds_iff {n : Type*} [Fintype n] [Nonempty n]
    (ν π w : n → ℝ) (hπ : ∀ i, 0 < π i) (α : ℝ) :
    (0 ≤ ν + α • π ∧ ν + α • π ≤ w) ↔
      (-minRatio ν π Finset.univ_nonempty ≤ α ∧
       α ≤ minRatio (w - ν) π Finset.univ_nonempty) := by
  have hl : (0 ≤ ν + α • π) ↔ -minRatio ν π Finset.univ_nonempty ≤ α := by
    have he : -minRatio ν π Finset.univ_nonempty ≤ α ↔
        -α ≤ minRatio ν π Finset.univ_nonempty := by constructor <;> intro h <;> linarith
    rw [he, le_minRatio_iff]
    change (∀ i, 0 ≤ ν i + α * π i) ↔ ∀ i, -α ≤ ν i / π i
    simp only [le_div_iff₀ (hπ _)]
    constructor <;> intro h i <;> nlinarith [h i]
  have hu : (ν + α • π ≤ w) ↔ α ≤ minRatio (w - ν) π Finset.univ_nonempty := by
    rw [le_minRatio_iff]
    change (∀ i, ν i + α * π i ≤ w i) ↔ ∀ i, α ≤ (w i - ν i) / π i
    simp only [le_div_iff₀ (hπ _)]
    constructor <;> intro h i <;> linarith [h i]
  exact and_congr hl hu

lemma equilibrium_bounds {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (w : n → ℝ) (hw : 0 ≤ w) (c x : n → ℝ)
    (hx : x ∈ equilibria P w c) : 0 ≤ x ∧ x ≤ w := by
  constructor
  · intro i
    rw [hx i]
    exact le_min (le_max_right _ _) (hw i)
  · intro i
    rw [hx i]
    exact min_le_right _ _

lemma equilibrium_of_linear {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (w c x : n → ℝ) (h0 : 0 ≤ x) (hw : x ≤ w)
    (hx : x = x ᵥ* P + c) : x ∈ equilibria P w c := by
  intro i
  have he : inflow P c x i = x i := by
    have h := congrFun hx i
    simpa [inflow, vecMul, dotProduct] using h.symm
  change x i = min (max (inflow P c x i) 0) (w i)
  have h0i : (0 : ℝ) ≤ x i := h0 i
  rw [he, max_eq_left h0i, min_eq_left (hw i)]

lemma linear_line {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (π ν c : n → ℝ) (hπP : π ᵥ* P = π)
    (hν : ν = ν ᵥ* P + c) (α : ℝ) :
    ν + α • π = (ν + α • π) ᵥ* P + c := by
  rw [add_vecMul, smul_vecMul, hπP]
  calc
    ν + α • π = (ν ᵥ* P + c) + α • π := congrArg (· + α • π) hν
    _ = _ := by abel

lemma linear_solutions_line {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (π : n → ℝ) (hπ0 : 0 ≤ π) (hπ : π ≠ 0) (hπP : π ᵥ* P = π)
    (c ν x : n → ℝ) (hν : ν = ν ᵥ* P + c) (hx : x = x ᵥ* P + c) :
    ∃ α : ℝ, x = ν + α • π := by
  have he : Pᵀ *ᵥ (x - ν) = (1 : ℝ) • (x - ν) := by
    rw [mulVec_transpose, sub_vecMul, one_smul]
    have h := congrArg₂ (· - ·) hx hν
    simpa using h.symm
  obtain ⟨α, hα⟩ := IrreducibleProof.eigenspace_one_dimensional Pᵀ
    (fun i j => hP j i) (IrreducibleProof.irreducible_transpose P hirr)
    1 π hπ0 hπ (by simpa [mulVec_transpose] using hπP) (x - ν) he
  refine ⟨α, ?_⟩
  have h := sub_eq_iff_eq_add.mp hα
  simpa [add_comm] using h

lemma linear_orthogonal {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (p c ν : n → ℝ) (hpP : P *ᵥ p = p)
    (hν : ν = ν ᵥ* P + c) : p ⬝ᵥ c = 0 := by
  have h := congrArg (fun v => v ⬝ᵥ p) hν
  rw [add_dotProduct, ← dotProduct_mulVec, hpP] at h
  rw [dotProduct_comm p c]
  linarith

lemma equilibria_segment {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (w : n → ℝ) (hw : 0 ≤ w) (c π : n → ℝ)
    (hπ0 : 0 ≤ π) (hπ : π ≠ 0) (hπpos : ∀ i, 0 < π i) (hπP : π ᵥ* P = π)
    (hlinear : ∀ x ∈ equilibria P w c, x = x ᵥ* P + c)
    (ν : n → ℝ) (hν : ν = ν ᵥ* P + c) :
    equilibria P w c = {x | ∃ α : ℝ,
      -minRatio ν π Finset.univ_nonempty ≤ α ∧
      α ≤ minRatio (w - ν) π Finset.univ_nonempty ∧ x = ν + α • π} := by
  ext x
  constructor
  · intro hx
    obtain ⟨α, rfl⟩ := linear_solutions_line P hP hirr π hπ0 hπ hπP c ν x hν (hlinear x hx)
    have hb := (line_bounds_iff ν π w hπpos α).mp (equilibrium_bounds P w hw c _ hx)
    exact ⟨α, hb.1, hb.2, rfl⟩
  · rintro ⟨α, hl, hu, rfl⟩
    have hb := (line_bounds_iff ν π w hπpos α).mpr ⟨hl, hu⟩
    exact equilibrium_of_linear P w c _ hb.1 hb.2 (linear_line P π ν c hπP hν α)

end SaturatedNet.Uniqueness.BalanceProof

open Matrix

namespace SaturatedNet.Uniqueness.BalanceProof

lemma characterization {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (hirr : IsIrreducible P)
    (w : n → ℝ) (hw : 0 ≤ w) (c p π : n → ℝ) (hpP : P *ᵥ p = p)
    (hπ0 : 0 ≤ π) (hπ : π ≠ 0) (hπpos : ∀ i, 0 < π i) (hπP : π ᵥ* P = π)
    (hlinear : (equilibria P w c).Nontrivial → ∀ x ∈ equilibria P w c, x = x ᵥ* P + c) :
    ((equilibria P w c).Nontrivial ↔
      (p ⬝ᵥ c = 0 ∧ ∃ ν : n → ℝ, ν = ν ᵥ* P + c ∧
        minRatio ν π Finset.univ_nonempty + minRatio (w - ν) π Finset.univ_nonempty > 0)) ∧
    ((equilibria P w c).Nontrivial →
      ∀ ν : n → ℝ, ν = ν ᵥ* P + c →
        equilibria P w c =
          {x | ∃ α : ℝ, -minRatio ν π Finset.univ_nonempty ≤ α ∧
            α ≤ minRatio (w - ν) π Finset.univ_nonempty ∧ x = ν + α • π}) := by
  have hsegment (hnt : (equilibria P w c).Nontrivial) (ν : n → ℝ)
      (hν : ν = ν ᵥ* P + c) :=
    equilibria_segment P hP hirr w hw c π hπ0 hπ hπpos hπP (hlinear hnt) ν hν
  refine ⟨⟨?_, ?_⟩, hsegment⟩
  · intro hnt
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hnt' : (equilibria P w c).Nontrivial := ⟨x, hx, y, hy, hxy⟩
    have hxl := hlinear hnt' x hx
    refine ⟨linear_orthogonal P p c x hpP hxl, x, hxl, ?_⟩
    have hs := hsegment hnt' x hxl
    rw [hs] at hx hy
    obtain ⟨α, hαl, hαu, hαx⟩ := hx
    obtain ⟨β, hβl, hβu, hβy⟩ := hy
    by_contra! hwidth
    have hαβ : α = β := by linarith
    apply hxy
    rw [hαx, hβy, hαβ]
  · rintro ⟨_, ν, hν, hwidth⟩
    let a := -minRatio ν π Finset.univ_nonempty
    let b := minRatio (w - ν) π Finset.univ_nonempty
    have hab : a < b := by dsimp [a, b]; linarith
    have ha := (line_bounds_iff ν π w hπpos a).mpr ⟨le_rfl, hab.le⟩
    have hb := (line_bounds_iff ν π w hπpos b).mpr ⟨hab.le, le_rfl⟩
    refine ⟨ν + a • π, equilibrium_of_linear P w c _ ha.1 ha.2 (linear_line P π ν c hπP hν a),
      ν + b • π, equilibrium_of_linear P w c _ hb.1 hb.2 (linear_line P π ν c hπP hν b), ?_⟩
    intro heq
    exact hab.ne ((smul_left_injective ℝ hπ) (add_left_cancel heq))

end SaturatedNet.Uniqueness.BalanceProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) [Nonempty n]
    (hirr : IsIrreducible P) (hρ : specRad P = 1)
    (p π : n → ℝ) (hp0 : 0 ≤ p) (hp : p ≠ 0) (hpP : P *ᵥ p = p)
    (hπ0 : 0 ≤ π) (hπ : π ≠ 0) (hπP : π ᵥ* P = π) :
    ((equilibria P w c).Nontrivial ↔
      (p ⬝ᵥ c = 0 ∧ ∃ ν : n → ℝ, ν = ν ᵥ* P + c ∧
        minRatio ν π Finset.univ_nonempty + minRatio (w - ν) π Finset.univ_nonempty > 0)) ∧
    ((equilibria P w c).Nontrivial →
      ∀ ν : n → ℝ, ν = ν ᵥ* P + c →
        equilibria P w c =
          {x | ∃ α : ℝ, -minRatio ν π Finset.univ_nonempty ≤ α ∧
            α ≤ minRatio (w - ν) π Finset.univ_nonempty ∧ x = ν + α • π}) := by
  have _ := hρ
  have hpp : ∀ i, 0 < p i :=
    IrreducibleProof.nonneg_eigenvector_pos P hP hirr 1 p hp0 hp (by simpa using hpP)
  have hπpos : ∀ i, 0 < π i :=
    IrreducibleProof.nonneg_eigenvector_pos Pᵀ (fun i j => hP j i)
      (IrreducibleProof.irreducible_transpose P hirr) 1 π hπ0 hπ
      (by simpa only [mulVec_transpose, one_smul] using hπP)
  exact BalanceProof.characterization P hP hirr w hw c p π hpP hπ0 hπ hπpos hπP
    (BalanceProof.equilibrium_linear_of_nontrivial P hP hirr p hpp hpP w hw c)

end SaturatedNet.Uniqueness
