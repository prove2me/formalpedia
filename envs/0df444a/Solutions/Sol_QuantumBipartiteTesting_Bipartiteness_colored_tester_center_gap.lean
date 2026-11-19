-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.colored_tester_center_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:16:05.527709+00:00
-- url     : https://prove2.me/submissions/f5c84b9e-7833-4584-a0d1-4c0b21a2863c

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_3_3
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_uniform_block_matching_contains
set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness.HardFamilyProof
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency.types false

private lemma matching_injective {M l : ℕ} (h : Fin M → Fin M) (hm : h ∈ Matchings M l) :
    Function.Injective h := by
  intro u v huv
  have hh := congrArg h huv
  simpa only [((mem_filter.mp hm).2.1 u).1,((mem_filter.mp hm).2.1 v).1] using hh

private lemma color_density {N M l colors : ℕ} (t : Fin N → Fin M) (ht : Function.Injective t)
    (h : Fin colors → (Fin M → Fin M)) (hm : ∀ c, h c ∈ Matchings M l) (c : Fin colors) :
    N ≤ 2*((VisibleEdges t h).filter (fun e => e.2.2 = c)).card+(M-N) := by
  let R := (univ : Finset (Fin N)).image t
  let C := (univ : Finset (Fin N)).filter (fun u => h c (t u) ∈ R)
  let E := (VisibleEdges t h).filter (fun e => e.2.2 = c)
  let I := E.biUnion (fun e => {e.1,e.2.1})
  have hR : R.card = N := by rw [card_image_of_injective _ ht]; simp
  have hmiss : (univ\C).card ≤ (univ\R).card := by
    apply card_le_card_of_injOn (fun u => h c (t u))
    · intro u hu
      have huC := (mem_sdiff.mp hu).2
      exact mem_sdiff.mpr ⟨mem_univ _,fun hh => huC (mem_filter.mpr ⟨mem_univ _,hh⟩)⟩
    · intro u hu v hv huv
      exact ht (matching_injective (h c) (hm c) huv)
  have hcover : C ⊆ I := by
    intro u hu
    obtain ⟨v,hv,hev⟩ := mem_image.mp ((mem_filter.mp hu).2)
    have heq : h c (t u) = t v := hev.symm
    have hne : u ≠ v := by
      intro huv
      subst v
      exact ((mem_filter.mp (hm c)).2.1 (t u)).2 heq
    rcases lt_or_gt_of_ne hne with huv | hvu
    · let e : ColoredEdge N colors := (u,v,c)
      have he : e ∈ E := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,huv,heq⟩,rfl⟩
      exact mem_biUnion.mpr ⟨e,he,by simp [e]⟩
    · let e : ColoredEdge N colors := (v,u,c)
      have hinv := ((mem_filter.mp (hm c)).2.1 (t u)).1
      rw [heq] at hinv
      have he : e ∈ E := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hvu,hinv⟩,rfl⟩
      exact mem_biUnion.mpr ⟨e,he,by simp [e]⟩
  have hI : I.card ≤ 2*E.card := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ e ∈ E, 2 := sum_le_sum (fun e he => card_le_two)
      _ = _ := by simp [Nat.mul_comm]
  have hC := (card_le_card hcover).trans hI
  have hcards : (univ\C).card+C.card = N := by
    simpa only [card_univ,Fintype.card_fin] using card_sdiff_add_card_eq_card (subset_univ C)
  have hout : (univ\R).card = M-N := by
    rw [card_sdiff_of_subset (subset_univ R),card_univ,Fintype.card_fin,hR]
  rw [hout] at hmiss
  dsimp only [E] at hC
  omega

private lemma visible_density {N M l : ℕ} (t : Fin N → Fin M) (ht : Function.Injective t)
    (h : Fin 3 → (Fin M → Fin M)) (hm : ∀ c, h c ∈ Matchings M l) :
    3*N ≤ 2*(VisibleEdges t h).card+3*(M-N) := by
  have hh := sum_le_sum (s := (univ : Finset (Fin 3))) (fun c hc => color_density t ht h hm c)
  have hcard : (VisibleEdges t h).card =
      ∑ c : Fin 3, ((VisibleEdges t h).filter (fun e => e.2.2 = c)).card :=
    card_eq_sum_card_fiberwise (fun e he => mem_univ e.2.2)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,sum_add_distrib,← Finset.mul_sum,← hcard] at hh
  exact hh

private lemma center_bounds (N : ℕ) : N ≤ Center N ∧ (Center N:ℝ) ≤ (11/10:ℝ)*N+4 := by
  have hlo := Nat.le_ceil ((11*N:ℝ)/40)
  have hup := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (11*N:ℝ)/40 by positivity)
  have hN := Nat.cast_nonneg (α := ℝ) N
  constructor
  · apply Nat.cast_le (α := ℝ) |>.mp
    unfold Center
    push_cast
    nlinarith
  · unfold Center
    push_cast
    nlinarith

private lemma center_density {N l : ℕ} (hN : 120 ≤ N)
    (t : Fin N → Fin (Center N)) (ht : Function.Injective t)
    (h : Fin 3 → (Fin (Center N) → Fin (Center N))) (hm : ∀ c, h c ∈ Matchings (Center N) l) :
    (13/10:ℝ)*N ≤ (VisibleEdges t h).card := by
  have hh := visible_density t ht h hm
  have hc := center_bounds N
  have hr : ((3*N:ℕ):ℝ) ≤ ((2*(VisibleEdges t h).card+3*(Center N-N):ℕ):ℝ) := Nat.cast_le.mpr hh
  push_cast [Nat.cast_sub hc.1] at hr
  have hN' : (120:ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

private lemma coordinate_div {l s : ℕ} (j : Fin l) (x : Fin s) :
    (finProdFinEquiv (j,x)).val/s = j.val := by
  exact congrArg (fun p : Fin l × Fin s => p.1.val) (finProdFinEquiv.symm_apply_apply (j,x))

private lemma embeddings_nonempty {N l s : ℕ} (hl : 0 < l) (b : Fin N → Fin l)
    (hcap : ∀ j, (univ.filter (fun v => b v = j)).card ≤ s) :
    (Embeddings (l*s) b).Nonempty := by
  have hemb (j : Fin l) : Nonempty ({v : Fin N // b v = j} ↪ Fin s) := by
    apply Function.Embedding.nonempty_iff_card_le.mpr
    simpa only [Fintype.card_subtype,Fintype.card_fin] using hcap j
  let f := fun j => Classical.choice (hemb j)
  let t := fun v : Fin N => finProdFinEquiv (b v,f (b v) ⟨v,rfl⟩)
  have ht : Function.Injective t := by
    intro u v h
    have hp := finProdFinEquiv.injective h
    have hb := congrArg Prod.fst hp
    have hs := congrArg Prod.snd hp
    have htransport (j : Fin l) (h : b v = j) : f (b v) ⟨v,rfl⟩ = f j ⟨v,h⟩ := by
      subst j
      rfl
    have hrw := htransport (b u) hb.symm
    exact congrArg Subtype.val ((f (b u)).injective (hs.trans hrw))
  refine ⟨t,mem_filter.mpr ⟨mem_univ _,ht,?_⟩⟩
  intro v
  rw [Nat.mul_div_cancel_left s hl]
  exact coordinate_div (b v) (f (b v) ⟨v,rfl⟩)

private lemma noOverflow_nonempty {N l s : ℕ} (hl : 0 < l) (hN : N ≤ l*s) :
    (univ.filter (NoOverflow N (l*s) l)).Nonempty := by
  let t : Fin N → Fin (l*s) := Fin.castLE hN
  let b := fun v => (finProdFinEquiv.symm (t v) : Fin l × Fin s).1
  refine ⟨b,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
  intro j
  rw [Nat.mul_div_cancel_left s hl]
  have hf : Function.Injective (fun v : {v : Fin N // b v = j} =>
      (finProdFinEquiv.symm (t v.val) : Fin l × Fin s).2) := by
    intro u v h
    apply Subtype.ext
    apply Fin.castLE_injective hN
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (u.property.trans v.property.symm) h
  have hh := Fintype.card_le_of_injective _ hf
  simpa only [Fintype.card_subtype,Fintype.card_fin] using hh

private lemma matchings_nonempty (l s : ℕ) (hl : 0 < l) (hs : Even s) :
    (Matchings (l*s) l).Nonempty := by
  by_contra h
  have he : Matchings (l*s) l = ∅ := not_nonempty_iff_eq_empty.mp h
  have hh := uniform_block_matching_contains l s hl hs (fun _ => ∅)
    (by simp) (by simp)
  simp only [he,Average,sum_empty,card_empty,Nat.cast_zero,zero_div,card_empty,prod_range_zero,prod_const_one] at hh
  norm_num at hh


private lemma xor_star {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    star (QAlgorithms.xorOracle f) = QAlgorithms.xorOracle (-f) := by
  ext ⟨i,y⟩ ⟨j,z⟩
  by_cases h : i = j
  · subst j
    simp [QAlgorithms.xorOracle, Matrix.star_apply, eq_add_neg_iff_add_eq, eq_comm]
  · simp [QAlgorithms.xorOracle, Matrix.star_apply, h, Ne.symm h]

private lemma xor_unitary {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    [AddCommGroup K] (f : I → K) :
    QAlgorithms.xorOracle f ∈ Matrix.unitaryGroup (I × K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, xor_star]
  exact QAlgorithms.xorOracle_mul_neg f

private lemma final_norm {I : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (A : Algorithm I k w q) (O : Matrix (I × Bits k) (I × Bits k) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (I × Bits k) ℂ) : ‖A.finalState O‖ = 1 := by
  have hK : Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ) ∈
      Matrix.unitaryGroup ((I × Bits k) × Fin w) ℂ :=
    Matrix.kronecker_mem_unitary hO (one_mem _)
  have hstate : ∀ t, ‖A.stateAt O t‖ = 1 := by
    apply Fin.induction
    · change ‖QAlgorithms.act (A.U 0 : Matrix _ _ ℂ) A.start‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U 0).property, A.start_unit]
    · intro i ih
      change ‖QAlgorithms.act (A.U i.succ : Matrix _ _ ℂ)
        (QAlgorithms.act (Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ))
          (A.stateAt O i.castSucc))‖ = 1
      rw [QAlgorithms.act_norm_of_mem_unitaryGroup (A.U i.succ).property,
        QAlgorithms.act_norm_of_mem_unitaryGroup hK, ih]
  exact hstate _

private lemma accept_bounds {I S : Type} [Fintype I] [DecidableEq I] {k w q : ℕ}
    (E : Encoding S k) (A : Algorithm I k w q)
    (out : (I × Bits k) × Fin w → Bool) (O : I → Option S) :
    0 ≤ Accept E A out O ∧ Accept E A out O ≤ 1 := by
  have hnorm := final_norm A _ (xor_unitary (E.code ∘ O))
  constructor
  · exact sum_nonneg (fun _ _ => sq_nonneg _)
  · unfold Accept QAlgorithms.QueryAlg.outputProb QAlgorithms.probEvent
    calc
      _ ≤ ∑ z, QAlgorithms.prob (A.finalState (QAlgorithms.xorOracle (E.code ∘ O))) z := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro z hz hz'
        exact sq_nonneg _
      _ = ‖A.finalState (QAlgorithms.xorOracle (E.code ∘ O))‖^2 := by
        simp only [QAlgorithms.prob, QAlgorithms.ket, EuclideanSpace.inner_single_left,
          EuclideanSpace.norm_sq_eq, map_one, one_mul]
      _ = 1 := by rw [hnorm]; norm_num


private def Other {n colors : ℕ} (e : ColoredEdge n colors) (u : Fin n) : Fin n :=
  if e.1 = u then e.2.1 else e.1

private lemma reconstruct {n colors : ℕ} (e : ColoredEdge n colors) (u : Fin n)
    (he : e.1 < e.2.1) (hu : Incident e u) :
    e = (min u (Other e u),max u (Other e u),e.2.2) := by
  rcases hu with h | h
  · subst u
    simp [Other,min_eq_left (le_of_lt he),max_eq_right (le_of_lt he)]
  · subst u
    simp [Other,ne_of_lt he,min_eq_right (le_of_lt he),max_eq_left (le_of_lt he)]


private lemma visible_other {N M colors : ℕ} (l : ℕ) (t : Fin N → Fin M)
    (h : Fin colors → (Fin M → Fin M)) (hm : ∀ j, h j ∈ Matchings M l)
    (e : ColoredEdge N colors) (he : e ∈ VisibleEdges t h) (u : Fin N) (hu : Incident e u) :
    h e.2.2 (t u) = t (Other e u) := by
  have helt := (mem_filter.mp he).2.1
  have heq := (mem_filter.mp he).2.2
  rcases hu with hu | hu
  · subst u
    simpa [Other] using heq
  · subst u
    have hinv := ((mem_filter.mp (hm e.2.2)).2.1 (t e.1)).1
    rw [heq] at hinv
    simpa [Other,ne_of_lt helt] using hinv

private lemma visible_consistent {N M colors : ℕ} (l : ℕ) (t : Fin N → Fin M)
    (ht : Function.Injective t) (h : Fin colors → (Fin M → Fin M))
    (hm : ∀ j, h j ∈ Matchings M l) : Consistent (VisibleEdges t h) := by
  refine ⟨fun e he => (mem_filter.mp he).2.1,?_⟩
  intro e he f hf hc hu
  obtain ⟨u,heu,hfu⟩ := hu
  have heq := visible_other l t h hm e he u heu
  have hfq := visible_other l t h hm f hf u hfu
  have ho : Other e u = Other f u := by
    apply ht
    rw [← heq,← hfq,hc]
  calc
    e = (min u (Other e u),max u (Other e u),e.2.2) := reconstruct e u (mem_filter.mp he).2.1 heu
    _ = (min u (Other f u),max u (Other f u),f.2.2) := by rw [ho,hc]
    _ = f := (reconstruct f u (mem_filter.mp hf).2.1 hfu).symm


private lemma average_const_nonempty {α : Type*} (S : Finset α) (hS : S.Nonempty) (c : ℝ) :
    Average S (fun _ => c) = c := by
  have hc : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  simp [Average,hc]


private lemma average_congr {α : Type*} (S : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ S, f x = g x) : Average S f = Average S g := by
  unfold Average
  congr 1
  exact sum_congr rfl h



private lemma average_mono {α : Type*} (S : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ S, f x ≤ g x) : Average S f ≤ Average S g := by
  unfold Average
  exact div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

private lemma average_interval {α : Type*} (S : Finset α) (hS : S.Nonempty) (f : α → ℝ)
    (lo hi : ℝ) (hf : ∀ x ∈ S, lo ≤ f x ∧ f x ≤ hi) : lo ≤ Average S f ∧ Average S f ≤ hi := by
  constructor
  · rw [← average_const_nonempty S hS lo]
    exact average_mono S _ _ (fun x hx => (hf x hx).1)
  · rw [← average_const_nonempty S hS hi]
    exact average_mono S _ _ (fun x hx => (hf x hx).2)

private lemma feasible_support_bounds {N colors M l : ℕ} (hv : ValidParameters N M l)
    (f : Finset (ColoredEdge N colors) → ℝ) (lo hi : ℝ)
    (hf : ∀ b : Fin N → Fin l, NoOverflow N M l b →
      ∀ t ∈ Embeddings M b, ∀ h : Fin colors → (Fin M → Fin M),
        (∀ c, h c ∈ Matchings M l) → lo ≤ f (VisibleEdges t h) ∧ f (VisibleEdges t h) ≤ hi) :
    lo ≤ FeasibleBase N M l f ∧ FeasibleBase N M l f ≤ hi := by
  have hl := hv.1
  obtain ⟨r,hr⟩ := hv.2.2
  have hM : M = l*(2*r) := by rw [hr]; ring
  rw [hM] at hv hf ⊢
  have heven : Even (2*r) := ⟨r,by omega⟩
  have hgood := noOverflow_nonempty hl hv.2.1
  obtain ⟨h₀,hh₀⟩ := matchings_nonempty l (2*r) hl heven
  have hmatch : (univ.filter (fun h : Fin colors → (Fin (l*(2*r)) → Fin (l*(2*r))) =>
      ∀ c, h c ∈ Matchings (l*(2*r)) l)).Nonempty :=
    ⟨fun _ => h₀,mem_filter.mpr ⟨mem_univ _,fun _ => hh₀⟩⟩
  unfold FeasibleBase MatchingAverage
  apply average_interval _ hgood
  intro b hb
  have hcap : ∀ j, (univ.filter (fun v => b v = j)).card ≤ 2*r := by
    simpa only [NoOverflow,Nat.mul_div_cancel_left (2*r) hl] using (mem_filter.mp hb).2
  have hEmb := embeddings_nonempty hl b hcap
  apply average_interval _ hEmb
  intro t ht
  apply average_interval _ hmatch
  intro h hh
  exact hf b (mem_filter.mp hb).2 t ht h (mem_filter.mp hh).2

private def ColoredTester {N k w q : ℕ} (ε : ℝ) (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N 3) k w q) (out : (Address N 3 × Bits k) × Fin w → Bool) : Prop :=
  ∀ F : Finset (ColoredEdge N), Consistent F → ∀ b : ColoredEdge N → Bool,
    (Balanced F b → 2/3 ≤ Accept E A out (LiftOracle (SignedResponse F b))) ∧
    (ε*N*3 ≤ (Frustration F b:ℝ) → Accept E A out (LiftOracle (SignedResponse F b)) ≤ 1/3)

private lemma yes_signing_bounds {N k w q : ℕ} (ε : ℝ) (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N 3) k w q) (out : (Address N 3 × Bits k) × Fin w → Bool)
    (hTest : ColoredTester ε E A out) (G : Finset (ColoredEdge N)) (hG : Consistent G) :
    2/3 ≤ SigningAverage .yes G (fun b => Accept E A out (LiftOracle (SignedResponse G b))) ∧
      SigningAverage .yes G (fun b => Accept E A out (LiftOracle (SignedResponse G b))) ≤ 1 := by
  unfold SigningAverage
  apply average_interval _ ⟨fun _ => false,mem_univ _⟩
  intro x hx
  have hb : Balanced G (fun e => xor (x e.1) (x e.2.1)) := ⟨x,fun e he => rfl⟩
  exact ⟨(hTest G hG _).1 hb,(accept_bounds E A out _).2⟩

private lemma average_add {α : Type*} (S : Finset α) (f g : α → ℝ) :
    Average S (fun x => f x+g x) = Average S f+Average S g := by
  unfold Average
  rw [sum_add_distrib,add_div]

private lemma no_signing_bounds {N k w q : ℕ} (ε : ℝ) (hε : ε ≤ 1/300)
    (E : Encoding (Fin N × Bool) k) (A : Algorithm (Address N 3) k w q)
    (out : (Address N 3 × Bits k) × Fin w → Bool) (hTest : ColoredTester ε E A out)
    (G : Finset (ColoredEdge N)) (hG : Consistent G) (hdense : (13/10:ℝ)*N ≤ G.card) :
    0 ≤ SigningAverage .no G (fun b => Accept E A out (LiftOracle (SignedResponse G b))) ∧
      SigningAverage .no G (fun b => Accept E A out (LiftOracle (SignedResponse G b))) ≤
        1/3+FrustrationTail G ((G.card:ℝ)/50) := by
  let sign := fun (b : {e // e ∈ G} → Bool) (e : ColoredEdge N) => if he : e ∈ G then b ⟨e,he⟩ else false
  have hfrac : ε*N*3 ≤ (G.card:ℝ)/50 := by
    have hh := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) N)
    nlinarith
  have hpoint (b : {e // e ∈ G} → Bool) :
      Accept E A out (LiftOracle (SignedResponse G (sign b))) ≤
        1/3+(if (Frustration G (sign b):ℝ) ≤ (G.card:ℝ)/50 then 1 else 0) := by
    by_cases hb : (Frustration G (sign b):ℝ) ≤ (G.card:ℝ)/50
    · rw [if_pos hb]
      linarith [(accept_bounds E A out (LiftOracle (SignedResponse G (sign b)))).2]
    · rw [if_neg hb,add_zero]
      exact (hTest G hG (sign b)).2 (hfrac.trans (le_of_lt (lt_of_not_ge hb)))
  unfold SigningAverage
  change 0 ≤ Average univ (fun b => Accept E A out (LiftOracle (SignedResponse G (sign b)))) ∧
    Average univ (fun b => Accept E A out (LiftOracle (SignedResponse G (sign b)))) ≤ _
  constructor
  · have hh := average_interval (univ : Finset ({e // e ∈ G} → Bool)) ⟨fun _ => false,mem_univ _⟩
      (fun b => Accept E A out (LiftOracle (SignedResponse G (sign b)))) 0 1
      (fun b hb => accept_bounds E A out _)
    exact hh.1
  · calc
      _ ≤ Average univ (fun b : {e // e ∈ G} → Bool =>
          1/3+(if (Frustration G (sign b):ℝ) ≤ (G.card:ℝ)/50 then 1 else 0)) :=
        average_mono _ _ _ (fun b hb => hpoint b)
      _ = _ := by
        rw [average_add,average_const_nonempty _ ⟨fun _ => false,mem_univ _⟩]
        congr 1
        simp only [Average,FrustrationTail,card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,
          Nat.cast_pow,Nat.cast_ofNat,sign]
        rw [← Finset.sum_filter]
        simp

end
end QuantumBipartiteTesting.Bipartiteness.HardFamilyProof

open QuantumBipartiteTesting.Bipartiteness
open QuantumBipartiteTesting.Bipartiteness.HardFamilyProof
open Finset Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

theorem solution : ∃ N₀ : ℕ, 120 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ε : ℝ, 0 < ε → ε ≤ 1/300 →
    ∀ k w q : ℕ, ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool,
      (∀ F : Finset (ColoredEdge N), Consistent F → ∀ b : ColoredEdge N → Bool,
        (Balanced F b → 2/3 ≤ Accept E A out (LiftOracle (SignedResponse F b))) ∧
        (ε*N*3 ≤ (Frustration F b:ℝ) → Accept E A out (LiftOracle (SignedResponse F b)) ≤ 1/3)) →
      (1/4:ℝ) ≤ FeasibleGap E A out (Center N) 1 := by
  obtain ⟨c,hc,htail⟩ := lemma_3_3.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : Tendsto (fun N : ℕ => (-c*Real.log 2)*(N:ℝ)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by nlinarith : -c*Real.log 2 < 0)).mpr tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => (2:ℝ)^(-c*N)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_atBot.comp hn
    change Tendsto (fun N : ℕ => Real.exp ((-c*Real.log 2)*(N:ℝ))) atTop (𝓝 0) at hh
    simpa only [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),Function.comp_apply,
      mul_assoc,mul_left_comm,mul_comm] using hh
  obtain ⟨Nt,hNt⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/12)))
  refine ⟨max Nt 120,by omega,?_⟩
  intro N hN ε hε hεmax k w q E A out hTest
  change ColoredTester ε E A out at hTest
  have hN120 : 120 ≤ N := by omega
  have hv : ValidParameters N (Center N) 1 := by
    refine ⟨by norm_num,(center_bounds N).1,?_⟩
    unfold Center
    omega
  have hyes := feasible_support_bounds hv
    (fun G : Finset (ColoredEdge N) => SigningAverage .yes G (fun b => Accept E A out (LiftOracle (SignedResponse G b))))
    (2/3) 1 (by
      intro b hb t ht h hm
      exact yes_signing_bounds ε E A out hTest _ (visible_consistent 1 t (mem_filter.mp ht).2.1 h hm))
  have hno := feasible_support_bounds hv
    (fun G : Finset (ColoredEdge N) => SigningAverage .no G (fun b => Accept E A out (LiftOracle (SignedResponse G b))))
    0 (1/3+(2:ℝ)^(-c*N)) (by
      intro b hb t ht h hm
      have hG := visible_consistent 1 t (mem_filter.mp ht).2.1 h hm
      have hdense := center_density hN120 t (mem_filter.mp ht).2.1 h hm
      have hs := no_signing_bounds ε hεmax E A out hTest _ hG hdense
      exact ⟨hs.1,hs.2.trans (add_le_add (le_refl (1/3:ℝ)) (htail N 3 _ hG hdense))⟩)
  have hy : (2/3:ℝ) ≤ FeasibleAcceptance E A out .yes (Center N) 1 := hyes.1
  have hn : FeasibleAcceptance E A out .no (Center N) 1 ≤ 1/3+(2:ℝ)^(-c*N) := hno.2
  have ht := hNt N (by omega)
  unfold FeasibleGap
  linarith
end
