-- Prove2me | solution 1 for SemAC02.Supplement.theorem_2_4_res_pc_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T05:52:49.278889+00:00
-- url     : https://prove2.me/submissions/db3cbcdb-27bc-462c-b9ab-5e6834aa7acf

import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_ResPC
import Definitions.Def_SemAC02_Supplement_IsSemPCRef

section
-- Inlined Solutions.ArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.ArithmeticCircuitBasics
end

section
-- Inlined Solutions.ExplicitPolynomialCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ExplicitPolynomialCircuits

open MvPolynomial ACirc ArithmeticCircuitBasics

noncomputable def monVars {F V : Type} (s : V →₀ ℕ) : List (ACirc F V) :=
  s.support.toList.flatMap (fun i => List.replicate (s i) (.var i))

noncomputable def monCirc {F V : Type} (s : V →₀ ℕ) : ACirc F V := .prod (monVars s)

noncomputable def polyCirc {F V : Type} [CommRing F] (f : MvPolynomial V F) : ACirc F V :=
  .sum (f.support.toList.map (fun s => (coeff s f,monCirc s)))

lemma monVars_length {F V : Type} (s : V →₀ ℕ) :
    (monVars (F := F) s).length = s.sum (fun _ e => e) := by
  simp [monVars,List.length_flatMap,Finsupp.sum]

lemma mem_monVars {F V : Type} (s : V →₀ ℕ) (c : ACirc F V) :
    c ∈ monVars s ↔ ∃ i ∈ s.support, c = .var i := by
  classical
  simp only [monVars,List.mem_flatMap,Finset.mem_toList,List.mem_replicate]
  constructor
  · rintro ⟨i,hi,hne,he⟩
    exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨i,hi,Finsupp.mem_support_iff.mp hi,he⟩

lemma toPoly_monCirc {F V : Type} [CommRing F] (s : V →₀ ℕ) :
    toPoly (monCirc (F := F) s) = monomial s 1 := by
  rw [monCirc,toPoly_prod]
  unfold monVars
  rw [List.map_flatMap]
  simp only [List.map_replicate,toPoly]
  rw [List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def,List.prod_replicate]
  rw [Finset.prod_map_toList]
  exact prod_X_pow_eq_monomial

lemma toPoly_polyCirc {F V : Type} [CommRing F] (f : MvPolynomial V F) : toPoly (polyCirc f) = f := by
  rw [polyCirc,toPoly_sum]
  simp only [List.map_map,Function.comp_def,toPoly_monCirc,C_mul_monomial,mul_one]
  rw [Finset.sum_map_toList]
  exact f.as_sum.symm

lemma monCirc_isMonGate {F V : Type} (s : V →₀ ℕ) (w : ℕ∞)
    (hs : ((s.sum (fun _ e => e) : ℕ) : ℕ∞) ≤ w) : IsMonGate w (monCirc (F := F) s) := by
  change ((monVars (F := F) s).length : ℕ∞) ≤ w ∧ ∀ c ∈ monVars s, IsLeaf c
  refine ⟨by rw [monVars_length]; exact hs,?_⟩
  intro c hc
  obtain ⟨i,hi,rfl⟩ := (mem_monVars s c).mp hc
  trivial

lemma polyCirc_layer {F V : Type} [CommRing F] (f : MvPolynomial V F) (w : ℕ∞)
    (hf : ((f.totalDegree : ℕ) : ℕ∞) ≤ w) : IsSumOf (IsMonGate w) (polyCirc f) := by
  intro q hq
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
  apply monCirc_isMonGate
  have hd : ((s.sum (fun _ e => e) : ℕ) : ℕ∞) ≤ (f.totalDegree : ℕ∞) := by
    exact_mod_cast le_totalDegree (Finset.mem_toList.mp hs)
  exact hd.trans hf

lemma subterms_monCirc {F V : Type} (s : V →₀ ℕ) (c : ACirc F V) :
    c ∈ subterms (monCirc s) ↔ c = monCirc s ∨ ∃ i ∈ s.support, c = .var i := by
  rw [monCirc,mem_subterms_prod]
  constructor
  · rintro (he | ⟨q,hq,hc⟩)
    · exact Or.inl he
    · obtain ⟨i,hi,rfl⟩ := (mem_monVars s q).mp hq
      exact Or.inr ⟨i,hi,by simpa only [subterms,Finset.mem_singleton] using hc⟩
  · rintro (he | ⟨i,hi,rfl⟩)
    · exact Or.inl he
    · exact Or.inr ⟨.var i,(mem_monVars s _).mpr ⟨i,hi,rfl⟩,by simp [subterms]⟩

lemma subterms_polyCirc {F V : Type} [CommRing F] (f : MvPolynomial V F) (c : ACirc F V)
    (hc : c ∈ subterms (polyCirc f)) :
    c = polyCirc f ∨ (∃ s ∈ f.support, c = monCirc s) ∨ ∃ i ∈ f.vars, c = .var i := by
  classical
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hq
    rcases (subterms_monCirc s c).mp hc with he | ⟨i,hi,he⟩
    · exact Or.inr (Or.inl ⟨s,Finset.mem_toList.mp hs,he⟩)
    · refine Or.inr (Or.inr ⟨i,?_,he⟩)
      rw [mem_vars]
      exact ⟨s,Finset.mem_toList.mp hs,hi⟩

end SemAC02.Supplement.ExplicitPolynomialCircuits
end

section
-- Inlined Solutions.ResPCCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ResPCCircuits

open MvPolynomial ACirc ArithmeticCircuitBasics ExplicitPolynomialCircuits

noncomputable def lineProduct {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) : ACirc F V :=
  .prod (D.map polyCirc)

noncomputable def lineCircuit {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) : ACirc F V :=
  .sum [(1,lineProduct D)]

lemma toPoly_lineProduct {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) :
    toPoly (lineProduct D) = D.prod := by
  simp only [lineProduct,toPoly_prod,List.map_map,Function.comp_def,toPoly_polyCirc]
  exact congrArg List.prod (List.map_id D)

lemma toPoly_lineCircuit {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) :
    toPoly (lineCircuit D) = D.prod := by
  simp only [lineCircuit,toPoly_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    C_1,one_mul,add_zero,toPoly_lineProduct]

lemma cval_lineCircuit {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) (x : V → Bool) :
    cval (lineCircuit D) x = (D.map (fun f => polyFn f x)).prod := by
  simp only [cval,polyFn,toPoly_lineCircuit,map_list_prod]

lemma line_zero_iff {F V : Type} [Field F] (D : List (MvPolynomial V F)) (x : V → Bool) :
    cval (lineCircuit D) x = 0 ↔ ResPCSat x D := by
  rw [cval_lineCircuit,List.prod_eq_zero_iff]
  simp only [List.mem_map,ResPCSat]

lemma line_layer {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) (w : ℕ∞)
    (hD : ∀ f ∈ D, ((f.totalDegree : ℕ) : ℕ∞) ≤ w) : IsSPSP w (lineCircuit D) := by
  intro q hq
  have hq' : q = (1,lineProduct D) := List.mem_singleton.mp hq
  subst q
  intro c hc
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hc
  exact polyCirc_layer f w (hD f hf)

lemma topTerms_lineCircuit {F V : Type} [CommRing F] (D : List (MvPolynomial V F)) :
    topTerms (lineCircuit D) = [lineProduct D] := rfl

lemma subterms_lineCircuit {F V : Type} [CommRing F] (D : List (MvPolynomial V F))
    (c : ACirc F V) (hc : c ∈ subterms (lineCircuit D)) :
    c = lineCircuit D ∨ c = lineProduct D ∨
      (∃ f ∈ D, c = polyCirc f) ∨
      (∃ f ∈ D, ∃ s ∈ f.support, c = monCirc s) ∨
      ∃ f ∈ D, ∃ i ∈ f.vars, c = .var i := by
  rcases (mem_subterms_sum c _).mp hc with he | ⟨q,hq,hc⟩
  · exact Or.inl he
  · have hq' : q = (1,lineProduct D) := List.mem_singleton.mp hq
    subst q
    rcases (mem_subterms_prod c _).mp hc with he | ⟨q,hq,hc⟩
    · exact Or.inr (Or.inl he)
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hq
      rcases subterms_polyCirc f c hc with he | ⟨s,hs,he⟩ | ⟨i,hi,he⟩
      · exact Or.inr (Or.inr (Or.inl ⟨f,hf,he⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,hf,s,hs,he⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f,hf,i,hi,he⟩)))

end SemAC02.Supplement.ResPCCircuits
end

section
-- Inlined Solutions.ResPCSemanticSimulation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ResPCSemanticSimulation

open MvPolynomial ACirc ResPCCircuits

theorem simulate {F V : Type} [Field F] (φ : LiftSAParity.CNF V)
    (π : List (List (MvPolynomial V F))) (hπ : IsSemResPCRef φ π) :
    IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx (φ : Set (LiftSAParity.Clause V))) (π.map lineCircuit) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro c hc
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hc
    exact line_layer D ⊤ (fun _ _ => le_top)
  · intro k hk
    have hkπ : k < π.length := by simpa only [List.length_map] using hk
    rcases hπ.1 k hkπ with ⟨C,hC,hperm⟩ | ⟨i,j,hi,hj,hinf⟩
    · refine Or.inl ⟨polyFn (clausePolyF C),⟨C,hC,rfl⟩,?_⟩
      intro x hx
      have hprod : (π[k]).prod = clausePolyF C := by
        calc
          _ = (C.toList.map litPolyF).prod := hperm.prod_eq
          _ = _ := Finset.prod_map_toList C litPolyF
      simpa only [List.getElem_map,cval,toPoly_lineCircuit] using congrArg (fun p => polyFn p x) hprod
    · refine Or.inr (Or.inr ⟨i,j,hi,hj,?_⟩)
      intro x hx h₁ h₂
      have h₁' : ResPCSat x π[i] := (line_zero_iff π[i] x).mp (by
        simpa only [List.getElem_map] using h₁)
      have h₂' : ResPCSat x π[j] := (line_zero_iff π[j] x).mp (by
        simpa only [List.getElem_map] using h₂)
      simpa only [List.getElem_map] using (line_zero_iff π[k] x).mpr (hinf x h₁' h₂')
  · refine ⟨lineCircuit [],?_,?_⟩
    · rw [List.getLast?_map,hπ.2]
      rfl
    · intro x hx
      simp only [cval_lineCircuit,List.map_nil,List.prod_nil]

theorem degree_preserved {F V : Type} [Field F]
    (π : List (List (MvPolynomial V F))) (w : ℕ)
    (hw : ∀ D ∈ π, ∀ f ∈ D, f.totalDegree ≤ w) :
    ∀ c ∈ π.map lineCircuit, IsSPSP (w : ℕ∞) c := by
  intro c hc
  obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hc
  apply line_layer
  intro f hf
  exact_mod_cast hw D hD f hf

end SemAC02.Supplement.ResPCSemanticSimulation
end

section
-- Inlined Solutions.ArithmeticProofCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticProofCounts

open ACirc

theorem topS_le_topOcc {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ topOcc π := by
  classical
  let ts := π.flatMap topTerms
  let G : Finset (Ω → F) := ts.toFinset.image (fun t => fun x : Ω => cval t x.1)
  have hsub : {g : Ω → F | g ≠ 0 ∧ ∃ c ∈ π, ∃ t ∈ topTerms c, g = fun x => cval t x.1} ⊆
      (↑G : Set (Ω → F)) := by
    rintro g ⟨hg,c,hc,t,ht,rfl⟩
    exact Finset.mem_image.mpr ⟨t,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,ht⟩),rfl⟩
  calc
    _ ≤ (↑G : Set (Ω → F)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet G)
    _ = G.card := Set.ncard_coe_finset _
    _ ≤ ts.toFinset.card := Finset.card_image_le
    _ ≤ ts.length := List.toFinset_card_le ts
    _ = _ := by simp only [ts,List.length_flatMap,topOcc]

end SemAC02.Supplement.ArithmeticProofCounts
end

section
-- Inlined Solutions.ResPCCircuitSize

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ResPCCircuitSize

open ACirc MvPolynomial ResPCCircuits ExplicitPolynomialCircuits

theorem size_bound {F V : Type} [CommRing F] (π : List (List (MvPolynomial V F))) :
    csize (π.map lineCircuit) ≤ 2*resPCSize π := by
  classical
  let Ls := π.toFinset
  let Ps := π.flatten.toFinset
  let Ms := Ps.biUnion (fun f => f.support)
  let Vs := Ps.biUnion (fun f => f.vars)
  let G₁ := Ls.image lineCircuit
  let G₂ := Ls.image lineProduct
  let G₃ := Ps.image polyCirc
  let G₄ := Ms.image (monCirc (F := F))
  let G₅ := Vs.image (ACirc.var (F := F))
  let S := G₁ ∪ G₂ ∪ G₃ ∪ G₄ ∪ G₅
  have hflat (D) (hD : D ∈ π) (f) (hf : f ∈ D) : f ∈ Ps :=
    List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨D,hD,hf⟩)
  have hsub : (π.map lineCircuit).toFinset.biUnion subterms ⊆ S := by
    intro c hc
    obtain ⟨q,hq,hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    rcases subterms_lineCircuit D c hc with he | he | ⟨f,hf,he⟩ | ⟨f,hf,s,hs,he⟩ | ⟨f,hf,i,hi,he⟩
    · have hm : c ∈ G₁ := Finset.mem_image.mpr ⟨D,List.mem_toFinset.mpr hD,he.symm⟩
      simp only [S,Finset.mem_union]
      aesop
    · have hm : c ∈ G₂ := Finset.mem_image.mpr ⟨D,List.mem_toFinset.mpr hD,he.symm⟩
      simp only [S,Finset.mem_union]
      aesop
    · have hm : c ∈ G₃ := Finset.mem_image.mpr ⟨f,hflat D hD f hf,he.symm⟩
      simp only [S,Finset.mem_union]
      aesop
    · have hs' : s ∈ Ms := Finset.mem_biUnion.mpr ⟨f,hflat D hD f hf,hs⟩
      have hm : c ∈ G₄ := Finset.mem_image.mpr ⟨s,hs',he.symm⟩
      simp only [S,Finset.mem_union]
      aesop
    · have hi' : i ∈ Vs := Finset.mem_biUnion.mpr ⟨f,hflat D hD f hf,hi⟩
      have hm : c ∈ G₅ := Finset.mem_image.mpr ⟨i,hi',he.symm⟩
      simp only [S,Finset.mem_union]
      aesop
  have hcard : S.card ≤ G₁.card+G₂.card+G₃.card+G₄.card+G₅.card := by
    have h₁ := Finset.card_union_le G₁ G₂
    have h₂ := Finset.card_union_le (G₁ ∪ G₂) G₃
    have h₃ := Finset.card_union_le (G₁ ∪ G₂ ∪ G₃) G₄
    have h₄ := Finset.card_union_le (G₁ ∪ G₂ ∪ G₃ ∪ G₄) G₅
    dsimp only [S]
    omega
  have h₁ : G₁.card ≤ Ls.card := Finset.card_image_le
  have h₂ : G₂.card ≤ Ls.card := Finset.card_image_le
  have h₃ : G₃.card ≤ Ps.card := Finset.card_image_le
  have h₄ : G₄.card ≤ Ms.card := Finset.card_image_le
  have h₅ : G₅.card ≤ Vs.card := Finset.card_image_le
  calc
    _ ≤ S.card := Finset.card_le_card hsub
    _ ≤ G₁.card+G₂.card+G₃.card+G₄.card+G₅.card := hcard
    _ ≤ _ := by
      change _ ≤ 2*(Ls.card+Ps.card+Ms.card+Vs.card)
      omega

theorem topS_bound {F V : Type} [CommRing F] (Ω : Set (V → Bool))
    (π : List (List (MvPolynomial V F))) : topS Ω (π.map lineCircuit) ≤ π.length := by
  apply (ArithmeticProofCounts.topS_le_topOcc Ω _).trans_eq
  simp [topOcc,List.map_map,Function.comp_def,topTerms_lineCircuit]

end SemAC02.Supplement.ResPCCircuitSize
end

section
-- Inlined Solutions.ResPCSimulation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ResPCSimulation

open ACirc ResPCCircuits

theorem simulation :
    ∃ K : ℝ, ∀ (F : Type) [Field F] (n : ℕ) (φ : LiftSAParity.CNF (Fin n))
      (π : List (List (MvPolynomial (Fin n) F))), IsSemResPCRef φ π →
      ∃ π' : List (ACirc F (Fin n)),
        IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        (csize π' : ℝ) ≤ K*resPCSize π ∧ topS Set.univ π' ≤ π.length ∧
        ∀ w : ℕ, (∀ D ∈ π, ∀ f ∈ D, f.totalDegree ≤ w) → ∀ c ∈ π', IsSPSP (w : ℕ∞) c := by
  refine ⟨2,?_⟩
  intro F inst n φ π hπ
  refine ⟨π.map lineCircuit,ResPCSemanticSimulation.simulate φ π hπ,?_,?_,?_⟩
  · exact_mod_cast ResPCCircuitSize.size_bound π
  · exact ResPCCircuitSize.topS_bound Set.univ π
  · exact ResPCSemanticSimulation.degree_preserved π

end SemAC02.Supplement.ResPCSimulation
end

open SemAC02.Supplement SemAC02.Supplement.ACirc

theorem solution :
    ∃ K : ℝ, ∀ (F : Type) [Field F] (n : ℕ) (φ : LiftSAParity.CNF (Fin n))
      (π : List (List (MvPolynomial (Fin n) F))), IsSemResPCRef φ π →
      ∃ π' : List (ACirc F (Fin n)),
        IsSemPCRef (IsSPSP ⊤) Set.univ (clauseAx (φ : Set (LiftSAParity.Clause (Fin n)))) π' ∧
        (csize π' : ℝ) ≤ K * resPCSize π ∧
        topS Set.univ π' ≤ π.length ∧
        ∀ w : ℕ, (∀ D ∈ π, ∀ f ∈ D, f.totalDegree ≤ w) → ∀ c ∈ π', IsSPSP (w : ℕ∞) c  := by
  exact SemAC02.Supplement.ResPCSimulation.simulation
