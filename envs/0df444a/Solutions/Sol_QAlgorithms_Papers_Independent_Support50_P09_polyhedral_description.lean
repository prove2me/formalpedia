-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.polyhedral_description
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:28:06.650979+00:00
-- url     : https://prove2.me/submissions/9be22e09-744b-47a6-a200-7225b5d9829d

import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_entropyThreshold_supermodular
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_corner_suffixCharacterization
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_vertex_maximalChain
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Support50.P09
open scoped BigOperators Matrix ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X9Geometry
private def reindexStar {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; exact Matrix.conjTranspose_reindex e e A
    map_smul' := by intros; rfl }

private lemma entropy_reindex {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    vnEntropy (Matrix.reindex e e A) = vnEntropy A := by
  let f : ℝ → ℝ := fun x => x * Real.logb 2 x
  let phi := reindexStar e
  have ht (B : Matrix I I ℂ) : (phi B).trace = B.trace :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hc : cfc f (phi A) = phi (cfc f A) := by
    by_cases hA : A.IsHermitian
    · have hphiA : (phi A).IsHermitian := hA.submatrix e.symm
      have hf : Continuous f := by
        simpa [f, Real.logb, mul_div_assoc] using
          Real.continuous_mul_log.div_const (Real.log 2)
      exact (StarAlgHomClass.map_cfc (S := ℂ) phi f A hf.continuousOn
        (by change Continuous (fun B : Matrix I I ℂ => B.submatrix e.symm e.symm); fun_prop)
        hA hphiA).symm
    · have hphiA : ¬ (phi A).IsHermitian := by
        intro h
        apply hA
        have hh := h.submatrix e
        convert hh using 1 <;> ext i j <;> simp [phi, reindexStar, Matrix.submatrix]
      have hz : cfc f A = 0 := cfc_apply_of_not_predicate A hA
      have hz' : cfc f (phi A) = 0 := cfc_apply_of_not_predicate (phi A) hphiA
      exact hz'.trans ((map_zero phi).symm.trans (congrArg phi hz.symm))
  change -(cfc f (phi A)).trace.re = -(cfc f A).trace.re
  rw [hc, ht]

private def emptyEquiv {m : ℕ} (D : Fin m → Type) (R : Type) :
    SubBasis D ∅ × R ≃ R where
  toFun a := a.2
  invFun r := (fun i => False.elim (Finset.notMem_empty i.val i.property), r)
  left_inv a := by
    apply Prod.ext
    · funext i; exact False.elim (Finset.notMem_empty i.val i.property)
    · rfl
  right_inv _ := rfl

private lemma entropyAt_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyAt rho ∅ = vnEntropy (traceLeft rho) := by
  have he : Matrix.reindex (emptyEquiv D R) (emptyEquiv D R)
      (registerMarginal rho ∅) = traceLeft rho := by
    ext a b
    change registerMarginal rho ∅ ((emptyEquiv D R).symm a)
      ((emptyEquiv D R).symm b) = traceLeft rho a b
    simp only [registerMarginal, Finset.notMem_empty, IsEmpty.forall_iff,
      not_false_eq_true, true_implies, implies_true, forall_true_iff, true_and]
    have h (x y : RegisterBasis D) : (∀ i, x i = y i) ↔ y = x :=
      ⟨fun h => (funext h).symm, fun h => by subst y; simp⟩
    change (∑ x : RegisterBasis D, ∑ y : RegisterBasis D,
      if (∀ i, x i = y i) then rho (x,a) (y,b) else 0) = _
    simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  unfold entropyAt
  convert (entropy_reindex (emptyEquiv D R) (registerMarginal rho ∅)).symm.trans
    (congrArg vnEntropy he) using 1

private lemma threshold_empty {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ) :
    entropyThreshold rho ∅ = 0 := by
  simp [entropyThreshold, entropyAt_empty]


private lemma mem_suffix {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (i : Fin m) :
    i ∈ senderSuffix pi l ↔ m ≤ (pi.symm i).val + l := by
  constructor
  · intro h
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp h
    have hj' := (Finset.mem_filter.mp hj).2
    have he : j = pi.symm i := by rw [← hji]; simp
    simpa [he] using hj'
  · intro h
    exact Finset.mem_image.mpr ⟨pi.symm i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h⟩, pi.apply_symm_apply i⟩

private lemma suffix_zero {m : ℕ} (pi : Equiv.Perm (Fin m)) :
    senderSuffix pi 0 = ∅ := by
  ext i
  simp only [mem_suffix, Nat.add_zero, Finset.notMem_empty, iff_false]
  omega

private lemma suffix_step {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    senderSuffix pi (l+1) =
      insert (pi ⟨m-l-1, by omega⟩) (senderSuffix pi l) := by
  ext i
  simp only [mem_suffix, Finset.mem_insert]
  have he : i = pi ⟨m-l-1, by omega⟩ ↔ (pi.symm i).val = m-l-1 := by
    rw [← Equiv.symm_apply_eq]
    exact Fin.ext_iff
  rw [he]
  have hi := (pi.symm i).isLt
  omega

private lemma step_notMem {m : ℕ} (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    pi ⟨m-l-1, by omega⟩ ∉ senderSuffix pi l := by
  rw [mem_suffix]
  simp only [Equiv.symm_apply_apply]
  omega

private lemma corner_step {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    {R : Type} [Fintype R]
    (rho : Matrix (RegisterBasis D × R) (RegisterBasis D × R) ℂ)
    (pi : Equiv.Perm (Fin m)) (l : ℕ) (hl : l < m) :
    compressionCorner rho pi (pi ⟨m-l-1, by omega⟩) =
      entropyThreshold rho (senderSuffix pi (l+1)) -
      entropyThreshold rho (senderSuffix pi l) := by
  let j : Fin m := ⟨m-l-1, by omega⟩
  have hlat : (Finset.univ.filter fun k : Fin m => j.val < k.val).image pi =
      senderSuffix pi l := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_suffix]
    constructor
    · rintro ⟨k,hk,rfl⟩
      simp only [Equiv.symm_apply_apply]
      dsimp [j] at hk
      omega
    · intro hi
      refine ⟨pi.symm i, ?_, pi.apply_symm_apply i⟩
      dsimp [j]
      have h := (pi.symm i).isLt
      omega
  change (entropyAt (trivialExtension (forgetEnvironment rho)) {pi j} +
    entropyAt rho ((Finset.univ.filter fun k : Fin m => (pi.symm (pi j)).val < k.val).image pi) -
    entropyAt rho (insert (pi j) _)) / 2 = _
  simp only [Equiv.symm_apply_apply]
  rw [hlat]
  rw [suffix_step pi l hl]
  unfold entropyThreshold
  rw [Finset.sum_insert (step_notMem pi l hl)]
  dsimp [j]
  ring


private def P {α : Type} [Fintype α] (f : Finset α → ℝ) : Set (α → ℝ) :=
  {x | ∀ S, f S ≤ ∑ a ∈ S, x a}

section Generic
variable {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)

private lemma P_closed : IsClosed (P f) := by
  have h : P f = ⋂ S : Finset α, {x | f S ≤ ∑ a ∈ S, x a} := by ext; simp [P]
  rw [h]
  exact isClosed_iInter fun S => isClosed_le continuous_const (by fun_prop)

private lemma P_convex : Convex ℝ (P f) := by
  intro x hx y hy a b ha hb hab S
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  calc
    f S = a * f S + b * f S := by rw [← add_mul, hab, one_mul]
    _ ≤ a * (∑ i ∈ S, x i) + b * (∑ i ∈ S, y i) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx S) ha) (mul_le_mul_of_nonneg_left (hy S) hb)

private lemma P_up {x v : α → ℝ} (hx : x ∈ P f) (hv : ∀ i, 0 ≤ v i) : x + v ∈ P f := by
  intro S
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  exact le_add_of_le_of_nonneg (hx S) (Finset.sum_nonneg fun i _ => hv i)

private lemma tight_union (hs : ∀ S T, f S + f T ≤ f (S ∪ T) + f (S ∩ T))
    {x : α → ℝ} (hx : x ∈ P f) {S T : Finset α}
    (hS : (∑ i ∈ S, x i) = f S) (hT : (∑ i ∈ T, x i) = f T) :
    (∑ i ∈ S ∪ T, x i) = f (S ∪ T) := by
  have he := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := x)
  have h := hs S T
  have hU := hx (S ∪ T)
  have hI := hx (S ∩ T)
  linarith

private lemma lower_base (h0 : f ∅ = 0)
    (hs : ∀ S T, f S + f T ≤ f (S ∪ T) + f (S ∩ T))
    {Q : α → ℝ} (hQ : Q ∈ P f) :
    ∃ x ∈ P f, x ≤ Q ∧ (∑ i, x i) = f Finset.univ := by
  let C := P f ∩ Set.Iic Q
  have hCclosed : IsClosed C := (P_closed f).inter isClosed_Iic
  have hCcompact : IsCompact C := by
    apply (isCompact_Icc : IsCompact (Set.Icc (fun i => f {i}) Q)).of_isClosed_subset hCclosed
    intro x hx
    exact ⟨fun i => by simpa using hx.1 {i}, hx.2⟩
  have hCne : C.Nonempty := ⟨Q, hQ, fun _ => le_rfl⟩
  obtain ⟨x, hx, hmin⟩ := hCcompact.exists_isMinOn hCne
    (show ContinuousOn (fun x : α → ℝ => ∑ i, x i) C by fun_prop)
  have hcover (i : α) : ∃ S, (∑ j ∈ S, x j) = f S ∧ i ∈ S := by
    by_contra hn
    push Not at hn
    have he (S : Finset α) : ∃ e : ℝ, 0 < e ∧
        e ≤ (∑ j ∈ S, x j) - f S ∨ i ∉ S := by
      by_cases hi : i ∈ S
      · have ht : f S < ∑ j ∈ S, x j := lt_of_le_of_ne (hx.1 S)
          (fun h => hn S h.symm hi)
        exact ⟨((∑ j ∈ S, x j) - f S), Or.inl ⟨sub_pos.mpr ht, le_rfl⟩⟩
      · exact ⟨1, Or.inr hi⟩
    have he' (S : Finset α) : ∃ e : ℝ, 0 < e ∧
        (i ∈ S → e ≤ (∑ j ∈ S, x j) - f S) := by
      obtain ⟨e, he⟩ := he S
      rcases he with he | hi
      · exact ⟨e, he.1, fun _ => he.2⟩
      · exact ⟨1, by norm_num, fun h => False.elim (hi h)⟩
    choose e he hb using he'
    obtain ⟨S₀, _, hleast⟩ := Finset.exists_min_image (Finset.univ : Finset (Finset α)) e (by simp)
    let d := e S₀
    have hd : 0 < d := he S₀
    let y : α → ℝ := fun j => x j - if j = i then d else 0
    have hy (S : Finset α) : (∑ j ∈ S, y j) = (∑ j ∈ S, x j) - if i ∈ S then d else 0 := by
      simp [y, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    have hyp : y ∈ P f := by
      intro S
      rw [hy]
      split_ifs with hi
      · have hh := (hleast S (Finset.mem_univ _)).trans (hb S hi)
        change d ≤ (∑ j ∈ S, x j) - f S at hh
        linarith
      · simpa using hx.1 S
    have hyx : y ≤ x := by intro j; dsimp [y]; split_ifs <;> linarith
    have hmin' : (∑ j, x j) ≤ ∑ j, y j := hmin ⟨hyp, hyx.trans hx.2⟩
    have hyt := hy Finset.univ
    simp only [Finset.mem_univ, if_true] at hyt
    linarith
  have htot (c : Finset (Finset α)) :
      (∀ S ∈ c, (∑ i ∈ S, x i) = f S) → (∑ i ∈ c.biUnion id, x i) = f (c.biUnion id) := by
    induction c using Finset.induction_on with
    | empty => simp [h0]
    | @insert S c hn ih =>
      intro h
      simpa using tight_union f hs hx.1 (h S (Finset.mem_insert_self _ _))
        (ih fun T hT => h T (Finset.mem_insert_of_mem hT))
  let c := Finset.univ.filter fun S : Finset α => (∑ i ∈ S, x i) = f S
  have hc : c.biUnion id = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨S, hS, hi⟩ := hcover i
    exact Finset.mem_biUnion.mpr ⟨S, by simp [c, hS], hi⟩
  refine ⟨x, hx.1, hx.2, ?_⟩
  rw [← hc]
  exact htot c (by simp [c])
end Generic

private lemma chain_permutation {m : ℕ} (K : Fin (m+1) → Finset (Fin m))
    (hK : IsMaximalChain K) :
    ∃ pi : Equiv.Perm (Fin m), ∀ l : Fin (m+1), senderSuffix pi l.val = K l := by
  have hm : Monotone K := Fin.monotone_iff_le_succ.mpr fun i => (hK.2.2 i).1
  let g : Fin (m+1) → Fin (m+1) := fun l =>
    ⟨(K l).card, by have hh := Finset.card_le_univ (s := K l); simpa using Nat.lt_succ_of_le hh⟩
  have hg : StrictMono g := Fin.strictMono_iff_lt_succ.mpr fun i =>
    Finset.card_lt_card (hK.2.2 i)
  have hc (l : Fin (m+1)) : (K l).card = l.val :=
    congrArg Fin.val (congrFun hg.eq_id l)
  have he (i : Fin m) : ∃ a, a ∉ K i.castSucc ∧ K i.succ = insert a (K i.castSucc) := by
    obtain ⟨a, ha, hn⟩ := Finset.exists_of_ssubset (hK.2.2 i)
    refine ⟨a, hn, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset ha (hK.2.2 i).1
    · rw [Finset.card_insert_of_notMem hn, hc, hc]
      rfl
  choose a ha hstep using he
  have hne (i j : Fin m) (hlt : i < j) : a i ≠ a j := by
    intro hij
    have hai : a i ∈ K i.succ := by rw [hstep]; simp
    have hsub := hm (show i.succ ≤ j.castSucc by simpa using hlt)
    exact ha j (hij ▸ hsub hai)
  have hainj : Function.Injective a := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim (hne i j hlt hij)
    · exact heq
    · exact False.elim (hne j i hgt hij.symm)
  let e : Equiv.Perm (Fin m) := Equiv.ofBijective a ⟨hainj, Finite.surjective_of_injective hainj⟩
  let pi := Fin.revPerm.trans e
  have hmem (l : Fin (m+1)) : ∀ i : Fin m, a i ∈ K l ↔ i.val < l.val := by
    induction l using Fin.induction with
    | zero => simp [hK.1]
    | succ l ih =>
      intro i
      rw [hstep, Finset.mem_insert, ih]
      have hi : a i = a l ↔ i = l := hainj.eq_iff
      rw [hi, Fin.ext_iff]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
  refine ⟨pi, fun l => ?_⟩
  apply Finset.ext
  intro b
  obtain ⟨i, rfl⟩ := e.surjective b
  rw [mem_suffix]
  have hv : (pi.symm (e i)).val = m - (i.val+1) := by
    simp [pi, Fin.revPerm, Fin.rev]
  rw [hv]
  change m ≤ m - (i.val+1) + l.val ↔ a i ∈ K l
  rw [hmem]
  have hi := i.isLt
  omega

private lemma suffix_unique {m : ℕ} (pi : Equiv.Perm (Fin m)) (x y : Fin m → ℝ)
    (h : ∀ l : ℕ, l ≤ m → (∑ i ∈ senderSuffix pi l, x i) = ∑ i ∈ senderSuffix pi l, y i) :
    x = y := by
  funext i
  let l := m - (pi.symm i).val - 1
  have hi := (pi.symm i).isLt
  have hl : l < m := by dsimp [l]; omega
  have hj : (⟨m-l-1, by omega⟩ : Fin m) = pi.symm i := by
    apply Fin.ext
    dsimp [l]
    omega
  have he := h (l+1) (by omega)
  rw [suffix_step pi l hl, Finset.sum_insert (step_notMem pi l hl),
    Finset.sum_insert (step_notMem pi l hl), h l (by omega)] at he
  rw [hj, Equiv.apply_symm_apply] at he
  linarith

private lemma corner_feasible {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (hm : 0 < m)
    (pi : Equiv.Perm (Fin m)) : compressionCorner (pureDensity phi) pi ∈ entropyPolyhedron (pureDensity phi) := by
  let f := entropyThreshold (pureDensity phi)
  let q := compressionCorner (pureDensity phi) pi
  have hs := entropyThreshold_supermodular phi hphi hm
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hz : S = ∅
    · subst S; simp [f, threshold_empty]
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S (fun i => (pi.symm i).val)
      (Finset.nonempty_iff_ne_empty.mpr hz)
    let T := S.erase i
    let L := (Finset.univ.filter fun j : Fin m => (pi.symm i).val < j.val).image pi
    have hiL : i ∉ L := by
      intro hin
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hin
      have hjlt := (Finset.mem_filter.mp hj).2
      have he : j = pi.symm i := by rw [← hji]; simp
      rw [he] at hjlt
      exact lt_irrefl _ hjlt
    have hTL : T ⊆ L := by
      intro j hj
      obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
      refine Finset.mem_image.mpr ⟨pi.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        pi.apply_symm_apply j⟩
      have hle := hmin j hjS
      have hne : (pi.symm j).val ≠ (pi.symm i).val := fun h => hji (pi.symm.injective (Fin.ext h))
      omega
    have hsum := ih T (Finset.erase_ssubset hi)
    have hsup := hs (insert i T) L
    have hU : insert i T ∪ L = insert i L := by
      ext j; simp only [Finset.mem_union, Finset.mem_insert]; grind
    have hI : insert i T ∩ L = T := by
      ext j; simp only [Finset.mem_inter, Finset.mem_insert]; grind
    rw [hU, hI] at hsup
    have hqi : q i = f (insert i L) - f L := by
      dsimp [q, compressionCorner, f, entropyThreshold, L]
      rw [Finset.sum_insert hiL]
      ring
    have hSi : insert i T = S := Finset.insert_erase hi
    rw [← hSi, Finset.sum_insert (Finset.notMem_erase i S)]
    change f (insert i T) ≤ q i + ∑ j ∈ T, q j
    dsimp [f] at hqi ⊢
    linarith


private lemma tight_endpoint (F sx sy a b : ℝ) (hx : F ≤ sx) (hy : F ≤ sy)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (he : a*sx+b*sy=F) : sx = F := by
  have hz : a*(sx-F)+b*(sy-F)=0 := by
    calc
      a*(sx-F)+b*(sy-F) = (a*sx+b*sy)-(a+b)*F := by ring
      _ = 0 := by rw [he, hab]; ring
  have hax := mul_nonneg ha.le (sub_nonneg.mpr hx)
  have hbx := mul_nonneg hb.le (sub_nonneg.mpr hy)
  have : a*(sx-F)=0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha.ne')

private lemma vertices_eq_corners {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (hm : 0 < m) :
    (entropyPolyhedron (pureDensity phi)).extremePoints ℝ = compressionCorners (pureDensity phi) := by
  apply Set.Subset.antisymm
  · intro Q hQ
    obtain ⟨K, hK, hsol⟩ := vertex_maximalChain phi hphi hm Q hQ
    obtain ⟨pi, hpi⟩ := chain_permutation K hK
    apply (corner_suffixCharacterization phi hphi hm Q).mpr
    refine ⟨pi, fun l hl hlm => ?_⟩
    let j : Fin m := ⟨l-1, by omega⟩
    have hj : j.succ = (⟨l, by omega⟩ : Fin (m+1)) := by apply Fin.ext; dsimp [j]; omega
    have hQc : chainEquations (pureDensity phi) K Q := by
      have : Q ∈ ({Q} : Set (Fin m → ℝ)) := rfl
      rwa [← hsol] at this
    rw [hpi ⟨l, by omega⟩, ← hj]
    exact hQc j
  · rintro Q ⟨pi, rfl⟩
    let rho := pureDensity phi
    let q := compressionCorner rho pi
    have hq := corner_feasible phi hphi hm pi
    -- Use the specific permutation rather than the existential characterization.
    have hqs (l : ℕ) (hl : l ≤ m) : (∑ i ∈ senderSuffix pi l, q i) = entropyThreshold rho (senderSuffix pi l) := by
      induction l with
      | zero => simp [suffix_zero, threshold_empty]
      | succ l ih =>
        have hlt : l < m := by omega
        rw [suffix_step pi l hlt, Finset.sum_insert (step_notMem pi l hlt), ih (by omega)]
        rw [← suffix_step pi l hlt]
        have hc := corner_step rho pi l hlt
        change q (pi ⟨m-l-1, by omega⟩) = _ at hc
        linarith
    refine ⟨hq, ?_⟩
    intro x hx y hy hseg
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    apply suffix_unique pi x q
    intro l hl
    have he := congrArg (fun z : Fin m → ℝ => ∑ i ∈ senderSuffix pi l, z i) heq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum] at he
    have hxx := hx (senderSuffix pi l)
    have hyy := hy (senderSuffix pi l)
    have ht := hqs l hl
    change a * (∑ i ∈ senderSuffix pi l, x i) + b * (∑ i ∈ senderSuffix pi l, y i) =
      ∑ i ∈ senderSuffix pi l, q i at he
    rw [ht] at he
    exact (tight_endpoint _ _ _ a b hxx hyy ha hb hab he).trans ht.symm

section GenericHull
variable {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)

private lemma base_representation (h0 : f ∅ = 0)
    (hs : ∀ S T, f S + f T ≤ f (S ∪ T) + f (S ∩ T))
    (V : Set (α → ℝ)) (hVfinite : V.Finite) (hv : (P f).extremePoints ℝ ⊆ V)
    {Q : α → ℝ} (hQ : Q ∈ P f) :
    ∃ x ∈ convexHull ℝ V, x ≤ Q := by
  let B := {x ∈ P f | (∑ i, x i) = f Finset.univ}
  have hBclosed : IsClosed B := (P_closed f).inter (isClosed_eq (by fun_prop) continuous_const)
  have hBcompact : IsCompact B := by
    apply (isCompact_Icc : IsCompact (Set.Icc (fun i => f {i})
      (fun i => f Finset.univ - f (Finset.univ.erase i)))).of_isClosed_subset hBclosed
    intro x hx
    refine ⟨fun i => by simpa using hx.1 {i}, fun i => ?_⟩
    have he := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    have hh := hx.1 (Finset.univ.erase i)
    have hxt : (∑ i, x i) = f Finset.univ := hx.2
    rw [hxt] at he
    linarith
  have hBconvex : Convex ℝ B := by
    intro x hx y hy a b ha hb hab
    refine ⟨P_convex f hx.1 hy.1 ha hb hab, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [hx.2, hy.2, ← add_mul, hab, one_mul]
  have hface : IsExtreme ℝ (P f) B := by
    refine ⟨fun _ hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    refine ⟨hx, ?_⟩
    have he := congrArg (fun z : α → ℝ => ∑ i, z i) heq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum] at he
    rw [hz.2] at he
    have hxx := hx Finset.univ
    have hyy := hy Finset.univ
    exact tight_endpoint _ _ _ a b hxx hyy ha hb hab he
  have hBhull : B ⊆ convexHull ℝ V := by
    rw [← closure_convexHull_extremePoints hBcompact hBconvex]
    apply closure_minimal
    · exact convexHull_mono (hface.extremePoints_subset_extremePoints.trans hv)
    · exact (hVfinite.isCompact_convexHull ℝ).isClosed
  obtain ⟨x, hx, hxQ, hxt⟩ := lower_base f h0 hs hQ
  exact ⟨x, hBhull ⟨hx, hxt⟩, hxQ⟩
end GenericHull

end X9Geometry

open X9Geometry

theorem solution {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] {R : Type} [Fintype R] [Nonempty R]
    (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1) (hm : 0 < m) :
    entropyPolyhedron (pureDensity phi) = vertexPolyhedron (pureDensity phi) ∧
    (entropyPolyhedron (pureDensity phi)).extremePoints ℝ = compressionCorners (pureDensity phi) ∧
    rateRecession (entropyPolyhedron (pureDensity phi)) = positiveCone m := by
  let rho := pureDensity phi
  let f := entropyThreshold rho
  have hs := entropyThreshold_supermodular phi hphi hm
  have hv := vertices_eq_corners phi hphi hm
  have hnonempty : ∃ q, q ∈ entropyPolyhedron rho :=
    ⟨compressionCorner rho (Equiv.refl _), corner_feasible phi hphi hm _⟩
  refine ⟨?_, hv, ?_⟩
  · ext Q
    constructor
    · intro hQ
      have hV : (compressionCorners rho).Finite := Set.finite_range _
      have hvertices : (P f).extremePoints ℝ ⊆ compressionCorners rho := by
        change (entropyPolyhedron (pureDensity phi)).extremePoints ℝ ⊆ _
        rw [hv]
      obtain ⟨x, hx, hxQ⟩ := base_representation f (threshold_empty rho) hs
        (compressionCorners rho) hV hvertices hQ
      refine ⟨x, hx, Q-x, ?_, ?_⟩
      · intro i; exact sub_nonneg.mpr (hxQ i)
      · abel
    · rintro ⟨x, hx, v, hv, rfl⟩
      have hxP : x ∈ P f := by
        apply convexHull_min (t := P f) ?_ (P_convex f) hx
        rintro q ⟨pi, rfl⟩
        exact corner_feasible phi hphi hm pi
      exact P_up f hxP hv
  · ext v
    constructor
    · intro hv
      intro i
      obtain ⟨q, hq⟩ := hnonempty
      by_contra hn
      have hvi : v i < 0 := lt_of_not_ge hn
      have hqi : f {i} ≤ q i := by simpa using hq {i}
      let t := (f {i} - q i - 1) / v i
      have ht : 0 ≤ t := (div_pos_of_neg_of_neg (by linarith) hvi).le
      have hh := hv q hq t ht {i}
      simp only [Finset.sum_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
      have he : t * v i = f {i} - q i - 1 := div_mul_cancel₀ _ hvi.ne
      change f {i} ≤ q i + t * v i at hh
      linarith
    · intro hv
      intro x hx t ht
      exact P_up f hx (fun i => mul_nonneg ht (hv i))
