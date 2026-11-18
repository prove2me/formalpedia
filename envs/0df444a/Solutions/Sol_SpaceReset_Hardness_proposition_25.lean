-- Prove2me | solution 1 for SpaceReset.Hardness.proposition_25
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T15:17:02.139904+00:00
-- url     : https://prove2.me/submissions/d1a76594-0816-427e-8c51-3f123ce4e523

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Trellis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SpaceReset.Hardness.SpanProof
open Matrix
lemma prefix_middle {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (B : Matrix κ (Fin n) F2) (u v : ℕ) (huv : u≤v) :
    prefixSpan B u ⊔ middleSpan B u v=prefixSpan B v := by
  unfold prefixSpan middleSpan colSpan
  rw [← Submodule.span_union,← Set.image_union]
  have hset : {j : Fin n|j.val<u} ∪ {j : Fin n|u≤j.val ∧ j.val<v}={j : Fin n|j.val<v} := by
    ext j
    simp only [Set.mem_union,Set.mem_setOf_eq]
    omega
  rw [hset]

lemma middle_suffix {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (B : Matrix κ (Fin n) F2) (u v : ℕ) (huv : u≤v) :
    middleSpan B u v ⊔ suffixSpan B v=suffixSpan B u := by
  unfold middleSpan suffixSpan colSpan
  rw [← Submodule.span_union,← Set.image_union]
  have hset : {j : Fin n|u≤j.val ∧ j.val<v} ∪ {j : Fin n|v≤j.val}={j : Fin n|u≤j.val} := by
    ext j
    simp only [Set.mem_union,Set.mem_setOf_eq]
    omega
  rw [hset]


end SpaceReset.Hardness.SpanProof
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.DirectSumProof

open Matrix SpanProof

variable {m : ℕ} {k : Fin m → ℕ}

/-- Projection of a block-indexed row vector onto block i. -/
def blockProj (i : Fin m) : (((j : Fin m) × Fin (k j)) → F2) →ₗ[F2] (Fin (k i) → F2) where
  toFun v a := v ⟨i,a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension of one block by zero on every other block. -/
def blockEmbed (i : Fin m) : (Fin (k i) → F2) →ₗ[F2] (((j : Fin m) × Fin (k j)) → F2) := by
  classical
  exact
    { toFun := fun v r=>if h:r.1=i then v (Fin.cast (congrArg k h) r.2) else 0
      map_add' := by
        intro v w
        funext r
        by_cases h:r.1=i <;> simp [h]
      map_smul' := by
        intro c v
        funext r
        by_cases h:r.1=i <;> simp [h] }

@[simp] lemma blockProj_embed (i : Fin m) (v : Fin (k i) → F2) :
    blockProj i (blockEmbed i v)=v := by
  classical
  funext a
  simp [blockProj,blockEmbed]

lemma blockProj_embed_off (i j : Fin m) (hij : i≠j) (v : Fin (k i) → F2) :
    blockProj j (blockEmbed i v)=0 := by
  classical
  funext a
  simp [blockProj,blockEmbed,Ne.symm hij]

lemma block_decomposition (v : ((j : Fin m) × Fin (k j)) → F2) :
    ∑ i, blockEmbed i (blockProj i v)=v := by
  classical
  funext r
  rcases r with ⟨j,a⟩
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [blockProj,blockEmbed]
  · intro i hi hij
    simp [blockProj,blockEmbed,Ne.symm hij]
  · simp

/-- Product of submodules in the dependent block coordinates. -/
def blockSpace (p : (i : Fin m) → Submodule F2 (Fin (k i) → F2)) :
    Submodule F2 (((j : Fin m) × Fin (k j)) → F2) where
  carrier := {v | ∀ i,blockProj i v∈p i}
  zero_mem' := by intro i;simpa using (p i).zero_mem
  add_mem' := by
    intro x y hx hy i
    exact (p i).add_mem (hx i) (hy i)
  smul_mem' := by
    intro c x hx i
    exact (p i).smul_mem c (hx i)

/-- The product submodule is the dependent function space of its component submodules. -/
def blockEquiv (p : (i : Fin m) → Submodule F2 (Fin (k i) → F2)) :
    blockSpace p ≃ₗ[F2] ((i : Fin m) → p i) :=
  { toFun := fun v i=>⟨blockProj i v.val,v.property i⟩
    invFun := fun v=>⟨fun r=>(v r.1).val r.2,fun i=>(v i).property⟩
    map_add' := by intros;rfl
    map_smul' := by intros;rfl
    left_inv := by intro v;rfl
    right_inv := by intro v;rfl }

lemma blockSpace_finrank (p : (i : Fin m) → Submodule F2 (Fin (k i) → F2)) :
    Module.finrank F2 (blockSpace p)=∑ i,Module.finrank F2 (p i) := by
  rw [(blockEquiv p).finrank_eq,Module.finrank_pi_fintype]

lemma blockSpace_inf (p q : (i : Fin m) → Submodule F2 (Fin (k i) → F2)) :
    blockSpace p ⊓ blockSpace q=blockSpace (fun i=>p i⊓q i) := by
  ext v
  constructor
  · rintro ⟨hp,hq⟩ i
    exact ⟨hp i,hq i⟩
  · intro h
    exact ⟨fun i=>(h i).1,fun i=>(h i).2⟩

lemma blockSpace_sup (p q : (i : Fin m) → Submodule F2 (Fin (k i) → F2)) :
    blockSpace p ⊔ blockSpace q=blockSpace (fun i=>p i⊔q i) := by
  classical
  apply le_antisymm
  · apply sup_le
    · intro v hv i
      exact Submodule.mem_sup_left (hv i)
    · intro v hv i
      exact Submodule.mem_sup_right (hv i)
  · intro v hv
    have h (i : Fin m) : ∃ x∈p i,∃ y∈q i,x+y=blockProj i v := (Submodule.mem_sup).mp (hv i)
    choose x hx y hy hxy using h
    let X : ((i : Fin m) × Fin (k i)) → F2 := fun r=>x r.1 r.2
    let Y : ((i : Fin m) × Fin (k i)) → F2 := fun r=>y r.1 r.2
    refine Submodule.mem_sup.mpr ⟨X,fun i=>hx i,Y,fun i=>hy i,?_⟩
    funext r
    exact congrFun (hxy r.1) r.2

variable {n : Fin m → ℕ}

/-- Columns of a given block that belong to a specified global column set. -/
def localColumns (S : Set (Fin (∑ i,n i))) (i : Fin m) : Set (Fin (n i)) :=
  {j | finSigmaFinEquiv ⟨i,j⟩∈S}

lemma directSum_column (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (i : Fin m) (j : Fin (n i)) :
    (fun r=>directSum G r (finSigmaFinEquiv ⟨i,j⟩))=blockEmbed i (fun a=>G i a j) := by
  classical
  let entry (p : (l : Fin m) × Fin (n l)) (r : (l : Fin m) × Fin (k l)) : F2 :=
    if h:p.1=r.1 then G r.1 r.2 (Fin.cast (congrArg n h) p.2) else 0
  change entry (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i,j⟩))=blockEmbed i (fun a=>G i a j)
  rw [Equiv.symm_apply_apply]
  funext r
  rcases r with ⟨l,a⟩
  by_cases h:i=l
  · subst l
    simp [entry,blockEmbed]
  · simp [entry,blockEmbed,h,Ne.symm h]

/-- The column span of a direct sum is exactly the product of the component column spans. -/
theorem directSum_colSpan (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (S : Set (Fin (∑ i,n i))) :
    colSpan (directSum G) S=blockSpace (fun i=>colSpan (G i) (localColumns S i)) := by
  classical
  apply le_antisymm
  · unfold colSpan
    apply Submodule.span_le.mpr
    rintro z ⟨c,hc,rfl⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := finSigmaFinEquiv.surjective c
    change (fun r=>directSum G r (finSigmaFinEquiv ⟨i,j⟩))∈
      blockSpace (fun l=>colSpan (G l) (localColumns S l))
    rw [directSum_column]
    intro l
    by_cases h:l=i
    · subst l
      rw [blockProj_embed]
      exact Submodule.subset_span ⟨j,hc,rfl⟩
    · rw [blockProj_embed_off i l (Ne.symm h)]
      exact Submodule.zero_mem _
  · intro v hv
    have hmap (i : Fin m) : (colSpan (G i) (localColumns S i)).map (blockEmbed i)≤
        colSpan (directSum G) S := by
      unfold colSpan
      rw [← Submodule.span_image]
      apply Submodule.span_le.mpr
      rintro z ⟨w,⟨j,hj,rfl⟩,rfl⟩
      rw [← directSum_column G i j]
      exact Submodule.subset_span ⟨finSigmaFinEquiv ⟨i,j⟩,hj,rfl⟩
    rw [← block_decomposition v]
    apply Submodule.sum_mem
    intro i hi
    exact hmap i (Submodule.mem_map_of_mem (hv i))

end SpaceReset.Hardness.DirectSumProof
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.DirectSumProof

open Matrix SpanProof

variable {m : ℕ}

def extendedLength (n : Fin m → ℕ) (t : ℕ) : ℕ := if h:t < m then n ⟨t,h⟩ else 0

def blockOffset (n : Fin m → ℕ) (i : Fin m) : ℕ :=
  ∑ t∈Finset.range i.val,extendedLength n t

lemma totalLength_range (n : Fin m → ℕ) : (∑ i,n i)=∑ t∈Finset.range m,extendedLength n t := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [extendedLength,i.isLt]

lemma finSigma_val (n : Fin m → ℕ) (i : Fin m) (j : Fin (n i)) :
    (finSigmaFinEquiv ⟨i,j⟩ : ℕ)=blockOffset n i+j.val := by
  rw [finSigmaFinEquiv_apply]
  apply congrArg (fun a=>a+j.val)
  unfold blockOffset
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a ha
  have hlt:a.val < m := by have := a.isLt;have := i.isLt;omega
  simp only [extendedLength,dif_pos hlt]
  exact congrArg n (Fin.ext rfl)

lemma blockOffset_end (n : Fin m → ℕ) (i : Fin m) :
    blockOffset n i+n i=∑ t∈Finset.range (i.val+1),extendedLength n t := by
  rw [Finset.sum_range_succ]
  simp [blockOffset,extendedLength,i.isLt]

lemma blockOffset_separated (n : Fin m → ℕ) (i j : Fin m) (h:i<j) :
    blockOffset n i+n i≤blockOffset n j := by
  rw [blockOffset_end]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by have hh : i.val<j.val := h;omega)
  · intros
    exact Nat.zero_le _

lemma blockOffset_end_le_total (n : Fin m → ℕ) (i : Fin m) :
    blockOffset n i+n i≤∑ j,n j := by
  rw [blockOffset_end,totalLength_range]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono i.isLt
  · intros
    exact Nat.zero_le _

/-- The number of columns of block i that precede global cut u. -/
def localCut (n : Fin m → ℕ) (i : Fin m) (u : ℕ) : ℕ := min (u-blockOffset n i) (n i)

lemma localCut_le (n : Fin m → ℕ) (i : Fin m) (u : ℕ) : localCut n i u≤n i := Nat.min_le_right _ _

lemma localCut_mono (n : Fin m → ℕ) (i : Fin m) (u v : ℕ) (h:u≤v) :
    localCut n i u≤localCut n i v := by unfold localCut;omega

lemma localCut_inside (n : Fin m → ℕ) (i : Fin m) (a : ℕ) (ha:a≤n i) :
    localCut n i (blockOffset n i+a)=a := by unfold localCut;omega

lemma localCut_before (n : Fin m → ℕ) (i : Fin m) (u : ℕ) (h:u≤blockOffset n i) :
    localCut n i u=0 := by unfold localCut;omega

lemma localCut_after (n : Fin m → ℕ) (i : Fin m) (u : ℕ) (h:blockOffset n i+n i≤u) :
    localCut n i u=n i := by unfold localCut;omega

lemma localColumns_prefix (n : Fin m → ℕ) (i : Fin m) (u : ℕ) :
    localColumns {c : Fin (∑ i,n i)|c.val<u} i={j : Fin (n i)|j.val<localCut n i u} := by
  ext j
  change ((finSigmaFinEquiv ⟨i,j⟩ : ℕ)<u) ↔ _
  rw [finSigma_val]
  simp only [localCut,Set.mem_setOf_eq]
  have := j.isLt
  omega

lemma localColumns_suffix (n : Fin m → ℕ) (i : Fin m) (u : ℕ) :
    localColumns {c : Fin (∑ i,n i)|u≤c.val} i={j : Fin (n i)|localCut n i u≤j.val} := by
  ext j
  change (u≤(finSigmaFinEquiv ⟨i,j⟩ : ℕ)) ↔ _
  rw [finSigma_val]
  simp only [localCut,Set.mem_setOf_eq]
  have := j.isLt
  omega

lemma localColumns_middle (n : Fin m → ℕ) (i : Fin m) (u v : ℕ) :
    localColumns {c : Fin (∑ i,n i)|u≤c.val ∧ c.val<v} i=
      {j : Fin (n i)|localCut n i u≤j.val ∧ j.val<localCut n i v} := by
  ext j
  change (u≤(finSigmaFinEquiv ⟨i,j⟩ : ℕ) ∧ (finSigmaFinEquiv ⟨i,j⟩ : ℕ)<v) ↔ _
  rw [finSigma_val]
  simp only [localCut,Set.mem_setOf_eq]
  have := j.isLt
  omega

variable {k n : Fin m → ℕ}

lemma prefixSpan_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u : ℕ) :
    prefixSpan (directSum G) u=blockSpace (fun i=>prefixSpan (G i) (localCut n i u)) := by
  unfold prefixSpan
  rw [directSum_colSpan]
  simp_rw [localColumns_prefix]

lemma suffixSpan_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u : ℕ) :
    suffixSpan (directSum G) u=blockSpace (fun i=>suffixSpan (G i) (localCut n i u)) := by
  unfold suffixSpan
  rw [directSum_colSpan]
  simp_rw [localColumns_suffix]

lemma middleSpan_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u v : ℕ) :
    middleSpan (directSum G) u v=blockSpace (fun i=>middleSpan (G i) (localCut n i u) (localCut n i v)) := by
  unfold middleSpan
  rw [directSum_colSpan]
  simp_rw [localColumns_middle]

/-- Single-cut dimension decomposes additively at the induced local cuts. -/
theorem cutDim_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u : ℕ) :
    cutDim (directSum G) u=∑ i,cutDim (G i) (localCut n i u) := by
  unfold cutDim
  rw [prefixSpan_directSum,suffixSpan_directSum,blockSpace_inf,blockSpace_finrank]

/-- Two-cut dimension decomposes additively at the induced local windows. -/
theorem windowDim_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u v : ℕ) :
    windowDim (directSum G) u v=∑ i,windowDim (G i) (localCut n i u) (localCut n i v) := by
  unfold windowDim
  rw [prefixSpan_directSum,suffixSpan_directSum,
    middleSpan_directSum,blockSpace_sup,blockSpace_sup,blockSpace_inf,blockSpace_inf,
    blockSpace_finrank,blockSpace_finrank,← Finset.sum_add_distrib]

end SpaceReset.Hardness.DirectSumProof
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.DirectSumProof

open Matrix SpanProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ}

lemma colSpan_mono (G : Matrix κ (Fin n) F2) {S T : Set (Fin n)} (h:S⊆T) : colSpan G S≤colSpan G T :=
  Submodule.span_mono (Set.image_mono h)

@[simp] lemma prefix_zero (G : Matrix κ (Fin n) F2) : prefixSpan G 0=⊥ := by
  unfold prefixSpan colSpan
  simp

@[simp] lemma suffix_zero (G : Matrix κ (Fin n) F2) : suffixSpan G 0=colSpan G Set.univ := by
  unfold suffixSpan
  simp

@[simp] lemma prefix_end (G : Matrix κ (Fin n) F2) : prefixSpan G n=colSpan G Set.univ := by
  unfold prefixSpan
  congr 1
  ext j
  simp [j.isLt]

@[simp] lemma suffix_end (G : Matrix κ (Fin n) F2) : suffixSpan G n=⊥ := by
  unfold suffixSpan colSpan
  have h : {j : Fin n|n≤j.val}=∅ := by ext j;simp
  rw [h]
  simp

lemma prefix_le_all (G : Matrix κ (Fin n) F2) (u : ℕ) : prefixSpan G u≤colSpan G Set.univ :=
  colSpan_mono G (Set.subset_univ _)

lemma suffix_le_all (G : Matrix κ (Fin n) F2) (u : ℕ) : suffixSpan G u≤colSpan G Set.univ :=
  colSpan_mono G (Set.subset_univ _)

@[simp] lemma cutDim_zero (G : Matrix κ (Fin n) F2) : cutDim G 0=0 := by
  simp [cutDim]

@[simp] lemma cutDim_end (G : Matrix κ (Fin n) F2) : cutDim G n=0 := by
  simp [cutDim]

lemma windowDim_zero (G : Matrix κ (Fin n) F2) (v : ℕ) :
    windowDim G 0 v=Module.finrank F2 (prefixSpan G v) := by
  unfold windowDim
  rw [prefix_middle G 0 v (Nat.zero_le v),middle_suffix G 0 v (Nat.zero_le v),prefix_zero,suffix_zero]
  rw [inf_eq_left.mpr (prefix_le_all G v)]
  simp

lemma windowDim_end (G : Matrix κ (Fin n) F2) (u : ℕ) (hu:u≤n) :
    windowDim G u n=Module.finrank F2 (suffixSpan G u) := by
  unfold windowDim
  rw [prefix_middle G u n hu,middle_suffix G u n hu,suffix_end,prefix_end]
  rw [inf_eq_right.mpr (suffix_le_all G u)]
  simp

@[simp] lemma windowDim_zero_zero (G : Matrix κ (Fin n) F2) : windowDim G 0 0=0 := by
  rw [windowDim_zero,prefix_zero]
  simp

@[simp] lemma windowDim_end_end (G : Matrix κ (Fin n) F2) : windowDim G n n=0 := by
  rw [windowDim_end G n le_rfl,suffix_end]
  simp

lemma finrank_colSpan_all (G : Matrix κ (Fin n) F2) :
    Module.finrank F2 (colSpan G Set.univ)=G.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  unfold colSpan
  rw [Set.image_univ]
  rfl

lemma windowDim_whole (G : Matrix κ (Fin n) F2) : windowDim G 0 n=G.rank := by
  rw [windowDim_zero,prefix_end,finrank_colSpan_all]

lemma windowDim_zero_le (G : Matrix κ (Fin n) F2) (v : ℕ) : windowDim G 0 v≤Fintype.card κ := by
  rw [windowDim_zero]
  simpa using (Submodule.finrank_le (prefixSpan G v))

lemma windowDim_end_le (G : Matrix κ (Fin n) F2) (u : ℕ) (hu:u≤n) :
    windowDim G u n≤Fintype.card κ := by
  rw [windowDim_end G u hu]
  simpa using (Submodule.finrank_le (suffixSpan G u))

lemma cutDim_le_cInv (G : Matrix κ (Fin n) F2) (u : ℕ) (hu:u≤n) : cutDim G u≤cInv G :=
  Finset.le_sup (Finset.mem_range.mpr (by omega))

lemma cInv_le (G : Matrix κ (Fin n) F2) (C : ℕ) (h:∀ u,u≤n → cutDim G u≤C) : cInv G≤C := by
  apply Finset.sup_le
  intro u hu
  exact h u (by simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hu))

lemma windowDim_le_PiInv (G : Matrix κ (Fin n) F2) (u v : ℕ) (huv:u≤v) (hv:v≤n) :
    windowDim G u v≤PiInv G := by
  unfold PiInv
  apply Finset.le_sup (s:=cutPairs n) (f:=fun p : ℕ×ℕ=>windowDim G p.1 p.2) (b:=(u,v))
  simp only [cutPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  omega

lemma PiInv_le (G : Matrix κ (Fin n) F2) (C : ℕ)
    (h:∀ u v,u≤v → v≤n → windowDim G u v≤C) : PiInv G≤C := by
  apply Finset.sup_le
  intro p hp
  simp only [cutPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp
  exact h p.1 p.2 hp.2 (by omega)

end SpaceReset.Hardness.DirectSumProof
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.DirectSumProof

open Matrix

variable {m : ℕ} {k n : Fin m → ℕ}

lemma localCut_earlier (i j : Fin m) (hji:j < i) (u : ℕ) (hu:blockOffset n i ≤ u) :
    localCut n j u=n j := by
  apply localCut_after
  exact (blockOffset_separated n j i hji).trans hu

lemma localCut_later (i j : Fin m) (hij:i < j) (u : ℕ) (hu:u ≤ blockOffset n i+n i) :
    localCut n j u=0 := by
  apply localCut_before
  exact hu.trans (blockOffset_separated n i j hij)

lemma cutDim_inside_block (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (i : Fin m) (a : ℕ) (ha:a ≤ n i) :
    cutDim (directSum G) (blockOffset n i+a)=cutDim (G i) a := by
  rw [cutDim_directSum,Finset.sum_eq_single i]
  · rw [localCut_inside n i a ha]
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with h|h
    · rw [localCut_earlier i j h,cutDim_end]
      omega
    · rw [localCut_later i j h,cutDim_zero]
      omega
  · simp

lemma windowDim_inside_block (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (i : Fin m) (a b : ℕ) (ha:a ≤ n i) (hb:b ≤ n i) :
    windowDim (directSum G) (blockOffset n i+a) (blockOffset n i+b)=windowDim (G i) a b := by
  rw [windowDim_directSum,Finset.sum_eq_single i]
  · rw [localCut_inside n i a ha,localCut_inside n i b hb]
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with h|h
    · rw [localCut_earlier i j h,localCut_earlier i j h,windowDim_end_end] <;> omega
    · rw [localCut_later i j h,localCut_later i j h,windowDim_zero_zero] <;> omega
  · simp

lemma cutDim_upper (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (u : ℕ) :
    cutDim (directSum G) u ≤ Finset.univ.sup (fun i=>cInv (G i)) := by
  classical
  rw [cutDim_directSum]
  by_cases h : ∃ i,0 < localCut n i u ∧ localCut n i u < n i
  · obtain ⟨i,hpos,hlt⟩ := h
    have hu0:blockOffset n i < u := by unfold localCut at hpos;omega
    have hu1:u < blockOffset n i+n i := by unfold localCut at hlt;omega
    rw [Finset.sum_eq_single i]
    · exact (cutDim_le_cInv (G i) _ (localCut_le n i u)).trans (Finset.le_sup (f:=fun j : Fin m=>cInv (G j)) (Finset.mem_univ i))
    · intro j hj hji
      rcases lt_or_gt_of_ne hji with h|h
      · rw [localCut_earlier i j h u (by omega),cutDim_end]
      · rw [localCut_later i j h u (by omega),cutDim_zero]
    · simp
  · have hz (i : Fin m) : cutDim (G i) (localCut n i u)=0 := by
      have hi : localCut n i u=0 ∨ localCut n i u=n i := by
        have := localCut_le n i u
        have hn : ¬(0 < localCut n i u ∧ localCut n i u < n i) := fun hh=>h ⟨i,hh⟩
        omega
      rcases hi with hi|hi
      · rw [hi,cutDim_zero]
      · rw [hi,cutDim_end]
    simp only [hz,Finset.sum_const_zero,Nat.zero_le]

theorem cInv_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) :
    cInv (directSum G)=Finset.univ.sup (fun i=>cInv (G i)) := by
  apply le_antisymm
  · apply cInv_le
    intro u hu
    exact cutDim_upper G u
  · apply Finset.sup_le
    intro i hi
    apply cInv_le
    intro a ha
    rw [← cutDim_inside_block G i a ha]
    apply cutDim_le_cInv
    have := blockOffset_end_le_total n i
    omega

lemma windowDim_upper (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (u v : ℕ) (huv:u ≤ v) :
    windowDim (directSum G) u v ≤ max (∑ i,k i) (Finset.univ.sup (fun i=>PiInv (G i))) := by
  classical
  rw [windowDim_directSum]
  by_cases h : ∃ i,0 < localCut n i u ∧ localCut n i v < n i
  · obtain ⟨i,hpos,hlt⟩ := h
    have hu0:blockOffset n i < u := by unfold localCut at hpos;omega
    have hv1:v < blockOffset n i+n i := by unfold localCut at hlt;omega
    rw [Finset.sum_eq_single i]
    · apply (windowDim_le_PiInv (G i) _ _ (localCut_mono n i u v huv) (localCut_le n i v)).trans
      exact (Finset.le_sup (f:=fun j : Fin m=>PiInv (G j)) (Finset.mem_univ i)).trans (le_max_right _ _)
    · intro j hj hji
      rcases lt_or_gt_of_ne hji with h|h
      · rw [localCut_earlier i j h u (by omega),localCut_earlier i j h v (by omega),windowDim_end_end]
      · rw [localCut_later i j h u (by omega),localCut_later i j h v (by omega),windowDim_zero_zero]
    · simp
  · apply (Finset.sum_le_sum (s:=Finset.univ) (f:=fun i=>windowDim (G i) (localCut n i u) (localCut n i v))
      (g:=k) ?_).trans (le_max_left _ _)
    intro i hi
    have he : localCut n i u=0 ∨ localCut n i v=n i := by
      have := localCut_le n i v
      have hn : ¬(0 < localCut n i u ∧ localCut n i v < n i) := fun hh=>h ⟨i,hh⟩
      omega
    rcases he with he|he
    · rw [he]
      simpa using windowDim_zero_le (G i) (localCut n i v)
    · rw [he]
      simpa using windowDim_end_le (G i) (localCut n i u) (localCut_le n i u)

lemma windowDim_whole_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (hG : ∀ i,FullRowRank (G i)) :
    windowDim (directSum G) 0 (∑ i,n i)=∑ i,k i := by
  rw [windowDim_directSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [localCut_before n i 0 (Nat.zero_le _),localCut_after n i _ (blockOffset_end_le_total n i),windowDim_whole]
  simpa only [FullRowRank,Fintype.card_fin] using hG i

theorem PiInv_directSum (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2)
    (hG : ∀ i,FullRowRank (G i)) :
    PiInv (directSum G)=max (∑ i,k i) (Finset.univ.sup (fun i=>PiInv (G i))) := by
  apply le_antisymm
  · apply PiInv_le
    intro u v huv hv
    exact windowDim_upper G u v huv
  · apply max_le
    · rw [← windowDim_whole_directSum G hG]
      exact windowDim_le_PiInv (directSum G) 0 _ (Nat.zero_le _) le_rfl
    · apply Finset.sup_le
      intro i hi
      apply PiInv_le
      intro a b hab hb
      have ha:a ≤ n i := hab.trans hb
      rw [← windowDim_inside_block G i a b ha hb]
      apply windowDim_le_PiInv
      · omega
      · have := blockOffset_end_le_total n i
        omega

/-- Public Proposition 25, with the original directSum and invariants. -/
theorem proposition_25 {m : ℕ} {k n : Fin m → ℕ}
    (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (hG : ∀ i,FullRowRank (G i)) :
    cInv (directSum G)=Finset.univ.sup (fun i=>cInv (G i)) ∧
      PiInv (directSum G)=max (∑ i,k i) (Finset.univ.sup (fun i=>PiInv (G i))) :=
  ⟨cInv_directSum G,PiInv_directSum G hG⟩

end SpaceReset.Hardness.DirectSumProof
end

open SpaceReset.Hardness

theorem solution {m : ℕ} {k n : Fin m → ℕ}
    (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (hG : ∀ i, FullRowRank (G i)) :
    cInv (directSum G) = Finset.univ.sup (fun i => cInv (G i)) ∧
    PiInv (directSum G) = max (∑ i, k i) (Finset.univ.sup (fun i => PiInv (G i))) :=
  DirectSumProof.proposition_25 G hG
