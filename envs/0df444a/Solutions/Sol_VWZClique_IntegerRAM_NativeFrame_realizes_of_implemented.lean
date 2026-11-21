-- Prove2me | solution 1 for VWZClique.IntegerRAM.NativeFrame.realizes_of_implemented
-- status  : ACCEPTED   (prove)
-- author  : @orz
-- created : 2026-11-20T14:07:29.361009+00:00
-- url     : https://prove2.me/submissions/528c3d5a-2384-4c85-9eb0-8c84a7795f63

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_NativeCliqueCompiler
import Definitions.Def_VWZClique_NativeProjectionContract
import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/- NativeFrame -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured

theorem different (d : ℕ) {a b : Field} (h : a ≠ b) : reg d a ≠ reg d b := by
  cases a <;> cases b <;> simp_all [reg,Field.offset] <;> omega

theorem reset_runs (W d : ℕ) (m : Memory) :
    ∃ o, Runs W (.atom (.sub (reg d .index) (reg d .index) (reg d .index))) m 1 o ∧
      o (reg d .index) = 0 ∧ ∀ a ≠ reg d .index, o a=m a := by
  refine ⟨_,.atom (.sub _ _ _ _),by simp [update],?_⟩
  intro a h; simp [update,h]

def reset (d : ℕ) : Command := .atom (.sub (reg d .index) (reg d .index) (reg d .index))

/-- The cursor's running sum is already in the return cell. -/
def finish : Command := .skip

def pop (d : ℕ) (lim : ℤ) : Command :=
  let flag := reg d .flag
  let acc := reg d .value
  let ix := reg d .index
  .seq (.atom (.mul flag (reg d .coefficient) (reg (d+1) .value)))
    (.seq (.atom (.add acc acc flag))
      (.seq (.atom (.one flag))
        (.seq (.atom (.add ix ix flag)) (.atom (.sub flag ix lim)))))

/-- The coefficient of this particular child was written by push, and stays
in the parent header over the recursive child call. -/
theorem pop_runs (W d : ℕ) (lim : Field) (hl : lim ≠ .flag) (ha : lim ≠ .value)
    (hi : lim ≠ .index) (m : Memory) :
    ∃ o, Runs W (pop d (reg d lim)) m 5 o ∧
      o (reg d .value) = m (reg d .value) + m (reg d .coefficient)*m (reg (d+1) .value) ∧
      o (reg d .index) = m (reg d .index)+1 ∧
      o (reg d .flag) = m (reg d .index)+1-m (reg d lim) ∧
      ∀ a, a≠reg d .value → a≠reg d .index → a≠reg d .flag → o a=m a := by
  let f := reg d .flag
  let z := reg d .value
  let ix := reg d .index
  let c := reg d .coefficient
  let v := reg (d+1) .value
  let l := reg d lim
  have zf : z ≠ f := different d (by decide)
  have iz : ix ≠ z := different d (by decide)
  have ifl : ix ≠ f := different d (by decide)
  have lf : l ≠ f := different d hl
  have lz : l ≠ z := different d ha
  have li : l ≠ ix := different d hi
  let m₁ := update m f (m c*m v)
  let m₂ := update m₁ z (m z+m c*m v)
  let m₃ := update m₂ f 1
  let m₄ := update m₃ ix (m ix+1)
  let o := update m₄ f (m ix+1-m l)
  have a : Runs W (.atom (.mul f c v)) m 1 m₁ := .atom (.mul _ _ _ _)
  have b : Runs W (.atom (.add z z f)) m₁ 1 m₂ := by
    simpa [m₁,m₂,update,zf] using Runs.atom (Step.add (W:=W) m₁ z z f)
  have e : Runs W (.atom (.one f)) m₂ 1 m₃ := .atom (.one _ _)
  have g : Runs W (.atom (.add ix ix f)) m₃ 1 m₄ := by
    simpa [m₄,m₃,m₂,m₁,update,ifl,iz] using Runs.atom (Step.add (W:=W) m₃ ix ix f)
  have t : Runs W (.atom (.sub f ix l)) m₄ 1 o := by
    simpa [o,m₄,m₃,m₂,m₁,update,lf,li,lz] using Runs.atom (Step.sub (W:=W) m₄ f ix l)
  refine ⟨o,a.seq (b.seq (e.seq (g.seq t))),?_,?_,?_,?_⟩
  · change o z=m z+m c*m v
    simp [o,m₄,m₃,m₂,update,zf,Ne.symm iz]
  · change o ix=m ix+1
    simp [o,m₄,update,ifl]
  · change o f=m ix+1-m l
    simp [o,update]
  · intro a az ai af
    change a≠z at az
    change a≠ix at ai
    change a≠f at af
    simp [o,m₄,m₃,m₂,m₁,update,af,az,ai]

end VWZClique.IntegerRAM.NativeFrame
end

/- FoldKernel -/
section
open VWZClique
namespace VWZClique.FoldProof

def post {L : ℕ} (m : Option (Mask L)) (x : PairBits L) : PairBits L :=
  match m with
  | none => x
  | some mask => (restore mask (fun r => r.2.2.1) x.2, restore mask (fun r => r.2.2.2) x.1)

theorem support {L : ℕ} (m : Mask L) (x y : PairBits L) :
    swapOK m x y ↔ pin (some m) Prod.fst x.1 ∧ pin (some m) (fun r => r.2.1) x.2 ∧
      y = post (some m) x := by
  constructor
  · intro h
    have fixed (i : Fin L) (r : Quad) (hi : m i = some r) := h i
    refine ⟨?_,?_,?_⟩
    · intro i r hr
      have hh := h i
      rcases r with ⟨s,u,v,t⟩
      simpa [hr] using congrArg Prod.fst (show (x.1 i,x.2 i,y.1 i,y.2 i) = (s,u,v,t) by simpa [hr] using hh)
    · intro i r hr
      rcases r with ⟨s,u,v,t⟩
      have hh := h i
      simp [hr] at hh
      exact hh.2.1
    · apply Prod.ext <;> funext i <;> have hh := h i <;>
        cases hm : m i with
        | none => simp [hm] at hh; simp [post,restore,hm]; grind
        | some r => rcases r with ⟨s,u,v,t⟩; simp [hm] at hh; simp [post,restore,hm]; grind
  · rintro ⟨h₁,h₂,rfl⟩ i
    cases h : m i with
    | none => simp [post,restore,h]
    | some r =>
      obtain ⟨s,u,v,t⟩ := r
      simp [post,restore,h,h₁ i _ h,h₂ i _ h]

theorem kernel_eq {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (x y : PairBits L) :
    maskKernel (F := F) m x y = if y = post m x then
      flag m Prod.fst x.1 * flag m (fun r => r.2.1) x.2 else 0 := by
  classical
  cases m with
  | none => simp [post,maskKernel,flag,pin,eq_comm]
  | some m =>
    simp only [maskKernel,support,flag]
    split_ifs <;> simp_all

theorem sum_kernels {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (f : PairBits L → PairBits L → PairBits L → PairBits L → F) :
    (∑ x, ∑ x', ∑ y, ∑ y', maskKernel a x x' * maskKernel b y y' * f x x' y y') =
    ∑ x, ∑ y, ((flag a Prod.fst x.1 * flag a (fun r => r.2.1) x.2) *
      (flag b Prod.fst y.1 * flag b (fun r => r.2.1) y.2)) * f x (post a x) y (post b y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp [kernel_eq, mul_ite, ite_mul]

end VWZClique.FoldProof
end

/- FoldRouting -/
section
open VWZClique
namespace VWZClique.FoldProof

def slotWord {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) (h : Fin 3) (i : Slot) : Bits L :=
  (route a b h i).2 (X (route a b h i).1)

abbrev Packed (L : ℕ) := Bits L × Bits L × Block L × PairBits L × PairBits L

def unpack {L : ℕ} (z : Packed L) : V → Bits L := fun v =>
  let p := (finProdFinEquiv (m := 3) (n := 3)).symm v
  (![block z.2.2.2.1 z.1, block z.2.2.2.2 z.2.1, z.2.2.1] p.1) p.2

@[simp] theorem unpack_site {L : ℕ} (z : Packed L) (g i : Fin 3) :
    unpack z (site g i) = (![block z.2.2.2.1 z.1,block z.2.2.2.2 z.2.1,z.2.2.1] g) i := by
  simp only [unpack,site,Equiv.symm_apply_apply]

def packEquiv (L : ℕ) : (V → Bits L) ≃ Packed L where
  toFun X := (X (site 0 2),X (site 1 2),fun i => X (site 2 i),
    (X (site 0 0),X (site 0 1)),(X (site 1 0),X (site 1 1)))
  invFun := unpack
  left_inv := by
    intro X
    funext v
    obtain ⟨⟨g,i⟩,rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective v
    fin_cases g <;> fin_cases i <;> rfl
  right_inv := by
    rintro ⟨z₁,z₂,c,x,y⟩
    simp [block, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem routed_slots {L : ℕ} (a b : Option (Mask L)) (z₁ z₂ : Bits L) (c : Block L)
    (x y : PairBits L) (h : Fin 3) (s : Slot) :
    slotWord a b (unpack (z₁,z₂,c,x,y)) h s =
    Sum.elim (![block x z₁,block (post b y) z₂,c] h)
      (![block y z₂,c,block (post a x) z₁] h) s := by
  cases s with
  | inl i => fin_cases h <;> fin_cases i <;> cases b <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]
  | inr i => fin_cases h <;> fin_cases i <;> cases a <;> simp [slotWord,route,adjust,perm,next,post,block,Fin.isValue]

noncomputable def unary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (v : Fin 3 × Slot) : F :=
  w (v.1,.inl (v.2,slotWord a b X v.1 v.2))

noncomputable def binary {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L)
    (w : ChannelKey L → F) (e : EdgeSlot) : F :=
  w (e.1,.inr (e.2.1,e.2.2,slotWord a b X e.1 e.2.1,slotWord a b X e.1 e.2.2))

theorem channels_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (z₁ z₂ : Bits L) (c : Block L) (x y : PairBits L) (w : ChannelKey L → F) :
    let X := unpack (z₁,z₂,c,x,y)
    placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block (post b y) z₂) c *
    placedChannel E w 2 c (block (post a x) z₁) =
    (∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e := by
  classical
  let X := unpack (z₁,z₂,c,x,y)
  let row := ![block x z₁,block (post b y) z₂,c]
  let col := ![block y z₂,c,block (post a x) z₁]
  have chan (h : Fin 3) : placedChannel E w h (row h) (col h) =
      (∏ s : Slot, unary a b X w (h,s)) * ∏ e ∈ E, if e.1=h then binary a b X w e else 1 := by
    unfold placedChannel unary binary
    dsimp only
    apply congrArg₂ (·*·)
    · simp only [X,row,col,routed_slots]
    · apply Finset.prod_congr rfl
      intro e he
      by_cases hh : e.1=h
      · subst h
        simp [X,row,col,routed_slots]
      · simp [hh]
  have allRows := Finset.prod_congr (s₁ := Finset.univ) rfl (fun h _ => chan h)
  rw [Finset.prod_mul_distrib] at allRows
  rw [Finset.prod_comm (f := fun h e => if e.1=h then binary a b X w e else 1)] at allRows
  simp only [Finset.prod_ite_eq,Finset.mem_univ,if_true] at allRows
  dsimp only
  rw [Fintype.prod_prod_type]
  convert! allRows using 1
  rw [Fin.prod_univ_three]
  rfl

noncomputable def checks {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (X : V → Bits L) : F :=
  (flag a Prod.fst (X (site 0 0)) * flag a (fun r => r.2.1) (X (site 0 1))) *
  (flag b Prod.fst (X (site 1 0)) * flag b (fun r => r.2.1) (X (site 1 1)))

private theorem five_sums {A B C D E F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [AddCommMonoid F] (f : A × B × C × D × E → F) :
    ∑ z, f z = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f (a,b,c,d,e) := by simp only [Fintype.sum_prod_type]

theorem reindexed {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (w : ChannelKey L → F) :
    placedFold E a b w = ∑ X : V → Bits L, checks a b X *
      ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  classical
  let expr := fun X : V → Bits L => checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e)
  rw [← (packEquiv L).symm.sum_comp expr]
  rw [five_sums (D := PairBits L) (E := PairBits L)]
  unfold placedFold
  apply Finset.sum_congr rfl
  intro z₁ _
  apply Finset.sum_congr rfl
  intro z₂ _
  apply Finset.sum_congr rfl
  intro c _
  let f := fun x x' y y' => placedChannel E w 0 (block x z₁) (block y z₂) *
    placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  have h := sum_kernels a b f
  dsimp only [f] at h
  simp only [mul_assoc] at h ⊢
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hc := channels_product a b E z₁ z₂ c x y w
  dsimp only at hc
  change _ = expr (unpack (z₁,z₂,c,x,y))
  unfold expr
  rw [← hc]
  simp [checks,block,mul_assoc,Fin.isValue]

end VWZClique.FoldProof
end

/- GraphWeights -/
section
open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.FoldProof

def weightAt {n : ℕ} (x : V → Fin n) : Kind → WeightKey n
  | .inl i => .inl (i,x i)
  | .inr (i,j) => .inr (i,j,x i,x j)

theorem value_at_ends {n : ℕ} (x : V → Fin n) (p : V × V) :
    addressValue (weightAt x (kind p)) p.1 = x p.1 ∧
    addressValue (weightAt x (kind p)) p.2 = x p.2 := by
  obtain ⟨i,j⟩ := p
  by_cases h : i=j
  · subst j; simp [kind,weightAt,addressValue]
  · by_cases h' : i < j <;> simp [kind,weightAt,addressValue,h,h',Ne.symm h]

theorem oriented (p : V × V) (i j : V) (h : kind p = .inr (i,j)) :
    i < j ∧ (p = (i,j) ∨ p = (j,i)) := by
  obtain ⟨u,v⟩ := p
  by_cases huv : u=v
  · simp [kind,huv] at h
  · by_cases hlt : u<v
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨hlt,Or.inl rfl⟩
    · simp [kind,huv,hlt] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm huv),Or.inr rfl⟩

end VWZClique.FoldProof
end

/- WeightedPlacement -/
section
open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

def ends (e : EdgeSlot) : V × V := (endpoint e.1 e.2.1, endpoint e.1 e.2.2)

theorem locate_ends : ∀ u v : V, ends (locate u v) = (u,v) := by decide

theorem chosen_ends (π : Equiv.Perm V) (p : V × V) :
    ends (chosen π p) = (π.symm p.1,π.symm p.2) ∨
      ends (chosen π p) = (π.symm p.2,π.symm p.1) := by
  by_cases h : π.symm p.1 ≤ π.symm p.2
  · simp [chosen,locate_ends,min_eq_left h,max_eq_right h]
  · simp [chosen,locate_ends,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]

theorem chosen_inj (π : Equiv.Perm V) (H : SimpleGraph V) : Set.InjOn (chosen π) (↑(pairs H)) := by
  classical
  intro p hp q hq he
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hq' := (Finset.mem_filter.mp hq).2.1
  have hinv (a b : V) : π.symm a = π.symm b ↔ a=b := π.symm.injective.eq_iff
  have h := congrArg ends he
  rcases chosen_ends π p with p1|p2 <;> rcases chosen_ends π q with q1|q2 <;>
    simp_all [Prod.ext_iff] <;> exact (lt_asymm hq' hp').elim

end VWZClique.WeightedProof
end

/- FoldEdges -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem folded_adj {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (e : EdgeSlot) (he : e ∈ E) (hne : (epPair a b e).1 ≠ (epPair a b e).2) :
    (foldedGraph a b E).Adj (epPair a b e).1 (epPair a b e).2 :=
  ⟨Finset.mem_image_of_mem (edgeImage a b) he, hne⟩

end VWZClique.FoldProof
end

/- UniformFolds -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

theorem route_static {L : ℕ} (a b : Option (Mask L)) (h : Fin 3) (s : Slot) :
    (route a b h s).1 =
      (route (representative a.isSome) (representative b.isSome) h s).1 := by
  cases s <;> fin_cases h <;> cases a <;> cases b <;> rfl

theorem graph_static {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot) (d : Branch)
    (ha : a.isSome = first d) (hb : b.isSome = second d) :
    foldedGraph a b E = child E d := by
  unfold child
  rw [← ha,← hb]
  unfold foldedGraph
  apply congrArg SimpleGraph.fromEdgeSet
  apply congrArg (fun T : Finset (Sym2 V) => (T : Set (Sym2 V)))
  apply Finset.image_congr
  intro e _
  change s((route a b e.1 e.2.1).1,(route a b e.1 e.2.2).1) = _
  rw [route_static a b e.1 e.2.1,route_static a b e.1 e.2.2]
  rfl

end VWZClique.UniformFolds
end

/- FoldFactors -/
section
open VWZClique
namespace VWZClique.FoldProof

theorem token_product {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (X : V → Bits L) (w : ChannelKey L → F) :
    (∏ v : FoldToken E, weight a b v (X (ends a b v).1) (X (ends a b v).2) w) =
    checks a b X * ((∏ v, unary a b X w v) * ∏ e ∈ E, binary a b X w e) := by
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  congr 1
  · rw [Fin.prod_univ_four]
    change ((flag a _ _ * flag a _ _) * flag b _ _) * flag b _ _ = _
    simp only [checks,mul_assoc]
    rfl
  · congr 1
    change (∏ e : ↥E, binary a b X w e.val) = _
    exact Finset.prod_attach E (binary a b X w)

end VWZClique.FoldProof
end

/- WeightedPadding -/
section
open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]

theorem weights_padded {n N : ℕ} (hn : n ≤ N) (H : SimpleGraph V) (w : WeightKey n → F) :
    weightedSum H (fun k : WeightKey N => literal w (padTag k)) = weightedSum H w := by
  classical
  let up : (V → Fin n) → V → Fin N := fun a i => (a i).castLE hn
  have inj : Function.Injective up := by
    intro a b h
    funext i
    exact Fin.ext (congrArg (fun x : Fin N => x.val) (congrFun h i))
  symm
  unfold weightedSum
  apply Fintype.sum_of_injective up inj
  · intro a ha
    have hex : ∃ i, ¬ (a i).val < n := by
      by_contra! h
      exact ha ⟨fun i => ⟨a i,h i⟩,rfl⟩
    obtain ⟨i,hi⟩ := hex
    have hz : (∏ j, literal w (padTag (Sum.inl (j,a j)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [padTag,hi,literal])
    simp [hz]
  · intro a
    simp [up,padTag,literal]

end VWZClique.WeightedProof
end

/- WeightedChannels -/
section
open VWZClique VWZClique.FoldProof
namespace VWZClique.WeightedProof

noncomputable def indexWord (L : ℕ) : Bits L ≃ Fin (2^L) :=
  Fintype.equivOfCardEq (by simp [Bits])

noncomputable def channelTag {F : Type*} [Field F] {L : ℕ}
    (π : Equiv.Perm V) (E : Finset EdgeSlot) : ChannelKey L → WeightKey (2^L) ⊕ F
  | (h,.inl (.inl i,x)) => .inl (.inl (π (site h i), indexWord L x))
  | (_,.inl (.inr _,_)) => .inr 1
  | (h,.inr (s,t,x,y)) => if (h,s,t) ∈ E then
      .inl (edgeKey (π (endpoint h s)) (π (endpoint h t)) (indexWord L x) (indexWord L y))
    else .inr 1

theorem supported {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (h : Fin 3) (a b : Block L) :
    let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
    channel inputs h a b = placedChannel E inputs h a b := by
  classical
  dsimp only
  unfold channel placedChannel
  dsimp only
  apply congrArg (fun y : F => _ * y)
  let x := Sum.elim a b
  let v := fun e : EdgeSlot => if e.1=h then literal w
    (channelTag π E (h,.inr (e.2.1,e.2.2,x e.2.1,x e.2.2))) else 1
  have addBack : (∏ e ∈ E, v e) = ∏ e : EdgeSlot, v e := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    by_cases h' : e.1=h
    · obtain ⟨k,s,t⟩ := e
      dsimp only at h'
      subst k
      simp [v,channelTag,he,literal]
    · simp [v,h']
  change _ = ∏ e ∈ E, v e
  rw [addBack,Fintype.prod_prod_type,Finset.prod_comm (f := fun k st => v (k,st))]
  simp only [v,Finset.prod_ite_eq',Finset.mem_univ,if_true]
  rw [Fintype.prod_prod_type]

theorem no_swap_word {L : ℕ} (X : V → Bits L) (h : Fin 3) (s : Slot) :
    slotWord none none X h s = X (endpoint h s) := by
  cases s with
  | inl i => fin_cases h <;> rfl
  | inr i => fin_cases h <;> rfl

theorem encode_graph {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (channelTag π (slots π H) j)) =
      weightedSum H w := by
  classical
  let E := slots π H
  let inputs := fun k : ChannelKey L => literal w (channelTag π E k)
  let perm := π.arrowCongr (indexWord L)
  rw [reindexed,weightedSum,← perm.sum_comp]
  apply Finset.sum_congr rfl
  intro X _
  let X' := perm X
  have mapped (v : V) : X' (π v) = indexWord L (X v) := by simp [X',perm,Equiv.arrowCongr_apply]
  have mapped' (v : V) : indexWord L (X (π.symm v)) = X' v := rfl
  have uv : (∏ v : Fin 3 × Slot, unary none none X inputs v) =
      ∏ i : V, w (.inl (i,X' i)) := by
    let u := fun i : V => w (Sum.inl (i,X' i))
    rw [← Equiv.prod_comp π u, ← (finProdFinEquiv (m:=3) (n:=3)).prod_comp (fun i => u (π i))]
    rw [Fintype.prod_prod_type,Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro h _
    rw [Fintype.prod_sum_type]
    simp only [unary,inputs,channelTag,literal,Sum.elim_inl,Sum.elim_inr,id_eq,
      Finset.prod_const_one,mul_one,no_swap_word,endpoint,u,mapped,site]
  have ev : (∏ e ∈ E, binary none none X inputs e) =
      ∏ i : V, ∏ j : V, if i < j ∧ H.Adj i j then w (.inr (i,j,X' i,X' j)) else 1 := by
    rw [← Fintype.prod_prod_type (fun p : V × V => if p.1<p.2 ∧ H.Adj p.1 p.2 then
      w (.inr (p.1,p.2,X' p.1,X' p.2)) else 1)]
    rw [← Finset.prod_filter]
    change (∏ e ∈ (pairs H).image (chosen π), binary none none X inputs e) =
      ∏ p ∈ pairs H, w (.inr (p.1,p.2,X' p.1,X' p.2))
    rw [Finset.prod_image (chosen_inj π H)]
    apply Finset.prod_congr rfl
    intro p hp
    let e := chosen π p
    have he : e ∈ E := Finset.mem_image_of_mem _ hp
    have hlt := (Finset.mem_filter.mp hp).2.1
    change literal w (channelTag π E (e.1,.inr (e.2.1,e.2.2,_,_))) = _
    simp only [channelTag,if_pos he,literal,Sum.elim_inl,no_swap_word]
    change w (edgeKey (π (ends e).1) (π (ends e).2) (indexWord L (X (ends e).1)) (indexWord L (X (ends e).2))) = _
    rcases chosen_ends π p with he|he
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,hlt,if_true,mapped']
    · dsimp only [e]
      simp only [he,Equiv.apply_symm_apply,edgeKey,not_lt_of_gt hlt,if_false,mapped']
  have checksOne : checks (F:=F) none none X = 1 := by simp [checks,flag,pin]
  change checks (F:=F) none none X * ((∏ v, unary none none X inputs v) *
      ∏ e ∈ E, binary none none X inputs e) = _
  rw [checksOne,one_mul,uv,ev]

end VWZClique.WeightedProof
end

/- CliqueDyadic -/
section
/-! Exact clearing of power-of-two denominators in integer matrix products. -/

namespace VWZClique.Dyadic
open scoped BigOperators

def value (q : ℕ) (z : ℤ) : ℚ := (z:ℚ)/(2:ℚ)^q

/-- Raising all entries to a common denominator preserves the exact rational. -/
theorem widen {q Q : ℕ} (h : q ≤ Q) (z : ℤ) :
    value Q (z * (2:ℤ)^(Q-q)) = value q z := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  simp [value, pow_add]
  field_simp

end VWZClique.Dyadic
end

/- UniformFoldWeights -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

/-- Reindexing every value table by the same domain permutation leaves the pattern sum unchanged. -/
def permuteKey {n : ℕ} (e : Equiv.Perm (Fin n)) : WeightKey n → WeightKey n
  | .inl (i,x) => .inl (i,e x)
  | .inr (i,j,x,y) => .inr (i,j,e x,e y)

theorem permute_domain {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V)
    (w : WeightKey n → F) (e : Equiv.Perm (Fin n)) :
    weightedSum H (fun k => w (permuteKey e k)) = weightedSum H w := by
  classical
  unfold weightedSum
  let p := (Equiv.refl V).arrowCongr e
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  change (∑ a, f (p a)) = ∑ a, f a
  exact p.sum_comp f

theorem inputKey_eq {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (E : Finset EdgeSlot)
    (w : WeightKey (2^L) → F) (k : ChannelKey L) :
    literal w (inputKey π E k) =
      literal (fun j => w (permuteKey ((indexWord L).symm.trans (wordIndex L)) j)) (channelTag π E k) := by
  rcases k with ⟨h,⟨s,x⟩|⟨s,t,x,y⟩⟩
  · cases s <;> simp [inputKey,channelTag,literal,permuteKey]
  · by_cases hs : (h,s,t) ∈ E
    · simp only [inputKey,channelTag,if_pos hs,literal,Sum.elim_inl]
      unfold edgeKey
      split <;> simp [permuteKey]
    · simp [inputKey,channelTag,literal,hs]

theorem input_exact {F : Type*} [Field F] {L : ℕ} (π : Equiv.Perm V) (H : SimpleGraph V)
    (w : WeightKey (2^L) → F) :
    placedFold (slots π H) none none (fun j : ChannelKey L => literal w (inputKey π (slots π H) j)) =
      weightedSum H w := by
  simp_rw [inputKey_eq]
  rw [encode_graph,permute_domain]

private theorem collect_identity {F I T : Type*} [Field F] [Fintype T] {n : ℕ}
    (H : SimpleGraph V) (ep : T → V × V)
    (edge : ∀ t, (ep t).1 ≠ (ep t).2 → H.Adj (ep t).1 (ep t).2)
    (f : T → Fin n → Fin n → (I → F) → F) (w : I → F) :
    weightedSum H (fun k => collect ep f k w) =
      ∑ x : V → Fin n, ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
  classical
  have take (x : V → Fin n) (b : Kind) : collect ep f (weightAt x b) w =
      ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = b), f t (x (ep t).1) (x (ep t).2) w := by
    have hs : shape (weightAt x b) = b := by cases b with | inl _ => rfl | inr v => rcases v with ⟨_,_⟩; rfl
    unfold collect
    rw [hs]
    refine Finset.prod_congr rfl ?_
    intro t ht
    have h := (Finset.mem_filter.mp ht).2
    subst b
    rw [(value_at_ends x (ep t)).1,(value_at_ends x (ep t)).2]
  have inactive (x : V → Fin n) (i j : V) (h : ¬ (i < j ∧ H.Adj i j)) :
      collect ep f (weightAt x (.inr (i,j))) w = 1 := by
    rw [take]
    apply Finset.prod_eq_one
    intro t ht
    obtain ⟨hlt,hp|hp⟩ := oriented _ _ _ (Finset.mem_filter.mp ht).2
    · have hadj := edge t (by simpa [hp] using hlt.ne)
      exact (h ⟨hlt, by simpa [hp] using hadj⟩).elim
    · have hadj := edge t (by simpa [hp] using hlt.ne')
      exact (h ⟨hlt, by simpa [hp] using hadj.symm⟩).elim
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro x _
  have allKeys : (∏ b : Kind, collect ep f (weightAt x b) w) =
      ∏ t : T, f t (x (ep t).1) (x (ep t).2) w := by
    simp_rw [take]
    exact Finset.prod_fiberwise _ _ _
  rw [← allKeys,Fintype.prod_sum_type,Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j ∧ H.Adj i j
  · simp [h,weightAt]
  · simpa only [if_neg h] using (inactive x i j h).symm

theorem updated_exact {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    weightedSum (foldedGraph a b E) (updated E a b w) = placedFold E a b w := by
  let ep := ends (E:=E) a b
  have he (t : FoldToken E) (hn : (ep t).1 ≠ (ep t).2) :
      (foldedGraph a b E).Adj (ep t).1 (ep t).2 := by
    rcases t with i|⟨h,i⟩|e
    · exact (hn rfl).elim
    · exact (hn rfl).elim
    · exact folded_adj a b E e.val e.property hn
  unfold updated
  rw [collect_identity (foldedGraph a b E) ep he,reindexed]
  let g := Equiv.piCongrRight (fun _ : V => (wordIndex L).symm)
  let f := fun X : V → Bits L => ∏ t : FoldToken E, weight a b t (X (ep t).1) (X (ep t).2) w
  change (∑ x, f (g x)) = _
  rw [g.sum_comp f]
  exact Finset.sum_congr rfl fun X _ => token_product a b E X w

theorem token_property {F : Type*} [Field F] {L : ℕ} (P : F → Prop)
    (pz : P 0) (po : P 1) (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → F) (pw : ∀ k, P (w k))
    (t : FoldToken E) (s u : Bits L) : P (weight a b t s u w) := by
  rcases t with i|⟨h,i⟩|e
  · have hh (m : Option (Mask L)) (rd : Quad → Bool) : P (flag m rd s) := by
      unfold flag
      split <;> assumption
    fin_cases i <;> exact hh _ _
  · exact pw _
  · exact pw _

theorem binary_prod {T : Type*} (s : Finset T) (f : T → ℚ)
    (h : ∀ t ∈ s, Binary (f t)) : Binary (∏ t ∈ s,f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Binary]
  | @insert i s hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp [Binary,hi,h₁,h₂]

theorem updated_binary {L : ℕ} (E : Finset EdgeSlot) (a b : Option (Mask L))
    (w : ChannelKey L → ℚ) (h : ∀ k, Binary (w k)) (k : WeightKey (2^L)) :
    Binary (updated E a b w k) := by
  apply binary_prod
  intro t _
  exact token_property Binary (Or.inl rfl) (Or.inr rfl) E a b w h t _ _

end VWZClique.UniformFolds
end

/- UniformFoldPaths -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

theorem Round.exact_value {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (d : Branch)
    (ha : r.a.isSome = first d) (hb : r.b.isSome = second d) :
    weightedSum (child (slots r.π r.H) d) (r.apply w) = placedFold (slots r.π r.H) r.a r.b (r.inputs w) := by
  rw [← graph_static r.a r.b _ d ha hb]
  exact updated_exact _ _ _ _

theorem Round.inputs_property {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ)
    (P : ℚ → Prop) (po : P 1) (hw : ∀ k, P (w k)) (j : ChannelKey L) : P (r.inputs w j) := by
  rcases j with ⟨h,⟨i,x⟩|⟨s,t,x,y⟩⟩
  · cases i
    · exact hw _
    · exact po
  · by_cases he : (h,s,t) ∈ slots r.π r.H
    · simpa only [Round.inputs,inputKey,if_pos he,literal,Sum.elim_inl] using hw
        (edgeKey (r.π (endpoint h s)) (r.π (endpoint h t)) (wordIndex L x) (wordIndex L y))
    · simpa only [Round.inputs,inputKey,if_neg he,literal,Sum.elim_inr,id_eq] using po

/-- For Boolean tables, the weighted sum counts a subset of the assignments. -/
theorem binary_sum {n : ℕ} (H : SimpleGraph V) (w : WeightKey n → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℕ, z ≤ n^9 ∧ weightedSum H w = (z:ℚ) := by
  classical
  let f := fun a : V → Fin n => (∏ i, w (.inl (i,a i))) *
    ∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1
  have hf (a : V → Fin n) : Binary (f a) := by
    have h₁ := binary_prod Finset.univ (fun i => w (.inl (i,a i))) (fun i _ => hw _)
    have h₂ : Binary (∏ i, ∏ j, if i<j ∧ H.Adj i j then w (.inr (i,j,a i,a j)) else 1) := by
      apply binary_prod
      intro i _
      apply binary_prod
      intro j _
      split
      · exact hw _
      · exact Or.inr rfl
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;> simp only [f,h₁,h₂,zero_mul,one_mul,Binary] <;> simp
  let s := Finset.univ.filter (fun a => f a=1)
  refine ⟨s.card,?_,?_⟩
  · simpa [V] using Finset.card_le_univ s
  · change (∑ a, f a) = (s.card:ℚ)
    calc
      _ = ∑ a, if f a=1 then (1:ℚ) else 0 := Finset.sum_congr rfl (fun a _ => by rcases hf a with h|h <;> simp [h])
      _ = _ := by rw [← Finset.sum_filter]; simp [s]

end VWZClique.UniformFolds
end

/- DyadicBounds -/
section
open VWZClique
namespace VWZClique.RankSwap

theorem denominator_bits {L : ℕ} (j : BasisLabel L) : denominatorExponent j ≤ L := by
  simpa [denominatorExponent] using Finset.card_le_univ (Finset.univ.filter (fun i => ¬j i < 2))

end VWZClique.RankSwap
end

/- WeightedAlgebra -/
section
open VWZClique
namespace VWZClique.WeightedProof

abbrev KernelArgs (L : ℕ) := PairBits L × PairBits L × PairBits L × PairBits L

noncomputable def evaluate {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (w : ChannelKey L → F) : (KernelArgs L → F) →ₗ[F] F where
  toFun k :=
    ∑ z₁ : Bits L, ∑ z₂ : Bits L, ∑ c : Block L,
      ∑ x : PairBits L, ∑ x' : PairBits L, ∑ y : PairBits L, ∑ y' : PairBits L,
        k (x,x',y,y') * placedChannel E w 0 (block x z₁) (block y z₂) *
          placedChannel E w 1 (block y' z₂) c * placedChannel E w 2 c (block x' z₁)
  map_add' f g := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum,mul_assoc]

def pairKernel {F : Type*} [Field F] {L : ℕ} (p q : PairBits L → PairBits L → F) :
    KernelArgs L → F := fun z => p z.1 z.2.1 * q z.2.2.1 z.2.2.2

private theorem evalMask {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) :
    evaluate E w (pairKernel (maskKernel a) (maskKernel b)) = placedFold E a b w := by
  rfl

private theorem evalProjection {F : Type*} [Field F] [CharZero F] {L : ℕ} (E : Finset EdgeSlot)
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → F) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    evaluate E w (pairKernel (projected Λ d) (projected Λ d)) = doubleProjection Λ Λ d d w := by
  unfold doubleProjection
  simp_rw [hc]
  rfl

theorem decomposition {F : Type*} [Field F] [CharZero F] {L M : ℕ}
    (Λ : Finset (BasisLabel L)) (d : BasisLabel L → ℚ)
    (m : Fin M → Mask L) (c : Fin M → ℤ)
    (hdecomp : ∀ x y : PairBits L,
      (if x = y then (1 : ℚ) else 0) =
        (∑ j ∈ Λ, d j * basisEntry j x * basisEntry j y) +
        ∑ i, (c i : ℚ) * swapEntry (m i) x y)
    (E : Finset EdgeSlot) (w : ChannelKey L → F)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w =
      doubleProjection Λ Λ (fun j => (d j : F)) (fun j => (d j : F)) w +
      (∑ i, (c i : F) * placedFold E (some (m i)) none w) +
      (∑ j, (c j : F) * placedFold E none (some (m j)) w) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) * placedFold E (some (m i)) (some (m j)) w := by
  classical
  let I := maskKernel (F := F) (L := L) none
  let R := projected Λ (fun j => (d j : F))
  let S := fun i => maskKernel (F := F) (some (m i))
  have hkernel (x y : PairBits L) : I x y = R x y + ∑ i, (c i : F) * S i x y := by
    have eqn := congrArg (fun q : ℚ => (q : F)) (hdecomp x y)
    simpa [I,R,S,maskKernel,projected,swapEntry,apply_ite] using eqn
  have hp : pairKernel I I = pairKernel R R +
      (∑ i, (c i : F) • pairKernel (S i) I) +
      (∑ j, (c j : F) • pairKernel I (S j)) -
      ∑ i, ∑ j, ((c i : F) * (c j : F)) • pairKernel (S i) (S j) := by
    funext z
    rcases z with ⟨x,x',y,y'⟩
    simp only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairKernel]
    simp only [← mul_assoc, ← Finset.sum_mul]
    have swap (j : Fin M) : (c j : F) * I x x' * S j y y' = I x x' * ((c j : F) * S j y y') := by ring
    have both (i j : Fin M) : (c i : F) * (c j : F) * S i x x' * S j y y' =
        ((c i : F) * S i x x') * ((c j : F) * S j y y') := by ring
    simp_rw [swap,both,← Finset.mul_sum,← Finset.sum_mul]
    rw [hkernel x x',hkernel y y']
    ring
  have he := congrArg (evaluate E w) hp
  simpa [I,R,S,map_sum,evalMask,evalProjection E Λ _ w hc] using he

end VWZClique.WeightedProof
end

/- UniformExpansion -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

attribute [instance] Expansion.finite

theorem windowExpansion_coefficients (K L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(((windowExpansion K L).coefficients i : ℤ) : ℝ)| ≤
      2^(lower K L)*4^(width K L)) ∧
    ∀ j : BasisLabel L, ∃ q : ℕ, q≤L ∧ ∃ z : ℤ,
      |(z:ℝ)| ≤ 1 + 3^L * (2^(lower K L)*4^(width K L)) ∧
      (windowExpansion K L).diagonal j = (z:ℚ)/2^q := by
  have hh := (Window.correct (lower K L) (width K L)).2.1
  exact ⟨fun i => term_bound hh i,fun j => ⟨denominatorExponent j,denominator_bits j,_,
    residual_bound (by positivity) hh j,rfl⟩⟩

theorem Expansion.decompose {L : ℕ} (q : Expansion L) (E : Finset EdgeSlot) (w : ChannelKey L → ℚ)
    (hc : ∀ h a b, channel w h a b = placedChannel E w h a b) :
    placedFold E none none w = doubleProjection q.labels q.labels q.diagonal q.diagonal w +
      (∑ i, (q.coefficients i : ℚ)*placedFold E (some (q.masks i)) none w) +
      (∑ j, (q.coefficients j : ℚ)*placedFold E none (some (q.masks j)) w) -
      ∑ i, ∑ j, ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*
        placedFold E (some (q.masks i)) (some (q.masks j)) w := by
  classical
  let e := (Fintype.equivFin q.Index).symm
  have hdecomp (x y : PairBits L) := q.identity x y
  have hx (x y : PairBits L) :
      (if x=y then (1:ℚ) else 0) =
        (∑ j ∈ q.labels, q.diagonal j * basisEntry j x * basisEntry j y) +
        ∑ i, (q.coefficients (e i) : ℚ)*swapEntry (q.masks (e i)) x y := by
    rw [e.sum_comp (fun i => (q.coefficients i : ℚ)*swapEntry (q.masks i) x y)]
    exact hdecomp x y
  have h := decomposition q.labels q.diagonal (fun i => q.masks (e i)) (fun i => q.coefficients (e i)) hx E w hc
  rw [e.sum_comp (fun i => (q.coefficients i : ℚ) * placedFold E (some (q.masks i)) none w),
    e.sum_comp (fun j => (q.coefficients j : ℚ) * placedFold E none (some (q.masks j)) w)] at h
  let f := fun i j => ((q.coefficients i : ℚ)*(q.coefficients j : ℚ))*placedFold E (some (q.masks i)) (some (q.masks j)) w
  have h₂ : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
    simp_rw [fun i => e.sum_comp (f (e i))]
    exact e.sum_comp (fun i => ∑ j,f i j)
  rw [h₂] at h
  simpa only [f,Rat.cast_id] using h

end VWZClique.UniformFolds
end

/- DoubleIdentity -/
section
open VWZClique

namespace VWZClique.Double

variable {F : Type*} [Field F] [CharZero F] {L : ℕ}

noncomputable def leftEntry (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) (u : Node Λ) (v : Node Γ) : F :=
  (d u.1 * e v.1) * ∑ y : PairBits L, (basisEntry v.1 y : F) *
    ∑ x : PairBits L, (basisEntry u.1 x : F) * channel w 0 (block x u.2) (block y v.2)

noncomputable def midEntry (Γ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (v : Node Γ) (c : Block L) : F :=
  ∑ y' : PairBits L, (basisEntry v.1 y' : F) * channel w 1 (block y' v.2) c

noncomputable def rightEntry (Λ : Finset (BasisLabel L)) (w : ChannelKey L → F)
    (c : Block L) (u : Node Λ) : F :=
  ∑ x' : PairBits L, (basisEntry u.1 x' : F) * channel w 2 c (block x' u.2)

private theorem projection_subtype (S : Finset (BasisLabel L)) (d : BasisLabel L → F)
    (x x' : PairBits L) :
    projected S d x x' = ∑ j : S, d j * (basisEntry j x : F) * (basisEntry j x' : F) := by
  exact (Finset.sum_attach S (fun j => d j * (basisEntry j x : F) * (basisEntry j x' : F))).symm

private theorem distribute (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (x x' y y' : PairBits L) (a b c : F) :
    projected Λ d x x' * projected Γ e y y' * a * b * c =
    ∑ j : Λ, ∑ k : Γ, ((d j * e k) * ((basisEntry k y : F) * ((basisEntry j x : F) * a))) *
      (((basisEntry k y' : F) * b) * ((basisEntry j x' : F) * c)) := by
  simp only [projection_subtype, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem reorder {Z C X J K R : Type*} [Fintype Z] [Fintype C] [Fintype X]
    [Fintype J] [Fintype K] [AddCommMonoid R]
    (f : Z → Z → C → X → X → X → X → J → K → R) :
    (∑ z, ∑ a, ∑ c, ∑ x, ∑ x', ∑ y, ∑ y', ∑ j, ∑ k, f z a c x x' y y' j k) =
    ∑ j, ∑ z, ∑ k, ∑ a, ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', f z a c x x' y y' j k := by
  let E : (J × Z × K × Z × C × X × X × X × X) ≃
      (Z × Z × C × X × X × X × X × J × K) :=
    { toFun := fun ⟨j,z,k,a,c,y,x,y',x'⟩ => (z,a,c,x,x',y,y',j,k)
      invFun := fun ⟨z,a,c,x,x',y,y',j,k⟩ => (j,z,k,a,c,y,x,y',x')
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g : Z × Z × C × X × X × X × X × J × K → R :=
    fun ⟨z,a,c,x,x',y,y',j,k⟩ => f z a c x x' y y' j k
  simpa only [Fintype.sum_prod_type, E, Equiv.coe_fn_mk, g] using (E.sum_comp g).symm

omit [CharZero F] in
private theorem contract_sums {C X : Type*} [Fintype C] [Fintype X]
    (q : F) (s : X → F) (a : X → X → F) (b : C → X → F) (h : C → X → F) :
    q * (∑ y, s y * ∑ x, a y x) * (∑ c, (∑ y', b c y') * ∑ x', h c x') =
    ∑ c, ∑ y, ∑ x, ∑ y', ∑ x', (q * (s y * a y x)) * (b c y' * h c x') := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum _ _ (s y), Finset.mul_sum _ _ q, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, Finset.mul_sum _ (b c), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x' _
  ring

/-- Expanding both projection kernels gives a three-matrix trace. -/
theorem trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F) (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w =
      ∑ u : Node Λ, ∑ v : Node Γ,
        leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u := by
  classical
  unfold doubleProjection
  simp_rw [distribute]
  rw [reorder]
  let f := fun (u : Node Λ) (v : Node Γ) =>
    leftEntry Λ Γ d e w u v * ∑ c : Block L, midEntry Γ w v c * rightEntry Λ w c u
  change _ = ∑ u : Node Λ, ∑ v : Node Γ, f u v
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  exact (contract_sums (d j * e k) (fun y => (basisEntry k y : F))
    (fun y x => (basisEntry j x : F) * channel w 0 (block x z) (block y a))
    (fun c y' => (basisEntry k y' : F) * channel w 1 (block y' a) c)
    (fun c x' => (basisEntry j x' : F) * channel w 2 c (block x' z))).symm

theorem matrix_trace_identity (Λ Γ : Finset (BasisLabel L)) (d e : BasisLabel L → F)
    (w : ChannelKey L → F) :
    doubleProjection Λ Γ d e w = Matrix.trace
      (Matrix.of (leftEntry Λ Γ d e w) *
        (Matrix.of (midEntry Γ w) * Matrix.of (rightEntry Λ w))) := by
  exact trace_identity Λ Γ d e w

end VWZClique.Double
end

/- UniformFoldEvaluator -/
section
open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

abbrev ProjectionEval (L : ℕ) := Expansion L → (ChannelKey L → ℚ) → ℚ

/-- Execute the same graph plan for every assignment-domain size.
    The two supplied subroutines evaluate sparse leaves and the pure projected term. -/
noncomputable def evaluatePlan {L : ℕ} (data : SimpleGraph V → Expansion L)
    (leaf : LeafEval L) (projection : ProjectionEval L) :
    {H : SimpleGraph V} → Plan H → (WeightKey (2^L) → ℚ) → ℚ
  | _,.leaf H hh,w => leaf H hh w
  | _,.split H π _ kids,w =>
    let q := data H
    let r := fun (a b : Option (Mask L)) => Round.mk H π a b
    let v := projection q ((r none none).inputs w)
    v + (∑ i, (q.coefficients i : ℚ) * evaluatePlan data leaf projection (kids .left)
          ((r (some (q.masks i)) none).apply w)) +
        (∑ j, (q.coefficients j : ℚ) * evaluatePlan data leaf projection (kids .right)
          ((r none (some (q.masks j))).apply w)) -
        ∑ i, ∑ j, ((q.coefficients i : ℚ) * (q.coefficients j : ℚ)) *
          evaluatePlan data leaf projection (kids .both)
            ((r (some (q.masks i)) (some (q.masks j))).apply w)

theorem input_supported {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) (h : Fin 3) (a b : Block L) :
    channel (r.inputs w) h a b = placedChannel (slots r.π r.H) (r.inputs w) h a b := by
  unfold Round.inputs
  simp_rw [inputKey_eq]
  exact supported _ _ _ _ _ _

theorem evaluatePlan_correct {L : ℕ} (data : SimpleGraph V → Expansion L)
    (leaf : LeafEval L) (projection : ProjectionEval L)
    (hl : ∀ H h w, leaf H h w = weightedSum H w)
    (hp : ∀ (q : Expansion L) w, projection q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w)
    {H : SimpleGraph V} (p : Plan H) (w : WeightKey (2^L) → ℚ) :
    evaluatePlan data leaf projection p w = weightedSum H w := by
  induction p generalizing w with
  | leaf H hh => exact hl H hh w
  | split H π hw kids ih =>
    let q := data H
    let E := slots π H
    let r (a b : Option (Mask L)) : Round L := ⟨H,π,a,b⟩
    let u := (r none none).inputs w
    have term (d : Branch) (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d) :
        evaluatePlan data leaf projection (kids d) ((r a b).apply w) = placedFold E a b u :=
      (ih d ((r a b).apply w)).trans ((r a b).exact_value w d ha hb)
    have he := q.decompose E u (input_supported (r none none) w)
    change projection q u +
        (∑ i, (q.coefficients i : ℚ) * evaluatePlan data leaf projection (kids .left)
          ((r (some (q.masks i)) none).apply w)) +
        (∑ j, (q.coefficients j : ℚ) * evaluatePlan data leaf projection (kids .right)
          ((r none (some (q.masks j))).apply w)) -
        (∑ i, ∑ j, ((q.coefficients i : ℚ) * (q.coefficients j : ℚ)) *
          evaluatePlan data leaf projection (kids .both)
            ((r (some (q.masks i)) (some (q.masks j))).apply w)) = _
    simp_rw [fun i => term .left (some (q.masks i)) none rfl rfl,
      fun j => term .right none (some (q.masks j)) rfl rfl,
      fun i j => term .both (some (q.masks i)) (some (q.masks j)) rfl rfl,hp]
    calc
      _ = placedFold E none none u := by simpa only [Rat.cast_id] using he.symm
      _ = _ := input_exact π H w

/-- Each projected contribution is the trace of the three explicit channel matrices. -/
noncomputable def traceProjection (L : ℕ) : ProjectionEval L := fun q w =>
  Matrix.trace (Matrix.of (Double.leftEntry q.labels q.labels q.diagonal q.diagonal w) *
    (Matrix.of (Double.midEntry q.labels w) * Matrix.of (Double.rightEntry q.labels w)))

theorem traceProjection_correct {L : ℕ} (q : Expansion L) (w : ChannelKey L → ℚ) :
    traceProjection L q w = doubleProjection q.labels q.labels q.diagonal q.diagonal w :=
  (Double.matrix_trace_identity _ _ _ _ _).symm

end VWZClique.UniformFolds
end

/- UniformFoldBudget -/
section
namespace VWZClique.UniformFolds

/-- The entire choice of real asymptotic parameters can be discarded after
writing these 37 pairs of natural numbers to a fixed finite table. -/
noncomputable def cutoffTable : Array (ℕ × ℕ) :=
  Array.ofFn (fun i : Fin 37 => (windowAt i.val,tileAt i.val))

theorem cutoffTable_spec (H : SimpleGraph V) :
    cutoffTable.size = 37 ∧
    cutoffTable[Nat.card H.edgeSet]? =
      some (windowAt (Nat.card H.edgeSet),tileAt (Nat.card H.edgeSet)) ∧
    4 < windowAt (Nat.card H.edgeSet) ∧ 0 < tileAt (Nat.card H.edgeSet) := by
  have he : Nat.card H.edgeSet < 37 := Nat.lt_succ_of_le (edge_limit H)
  exact ⟨by simp [cutoffTable],by simp only [cutoffTable,Array.getElem?_ofFn,dif_pos he],
    (selectCut _).window_large,(selectCut _).tile_pos⟩

end VWZClique.UniformFolds
end

/- TraceDyadicData -/
section
namespace VWZClique.TraceDyadic
open RankSwap UniformFolds Double

/-- The assignment side and common denominator of each diagonal residual. -/
def D (L : ℕ) : ℤ := 2^L

private theorem digit_cast (j : Fin 4) (s u : Bool) : (digit j s u : ℚ) = oneBit j s u := by
  fin_cases j <;> cases s <;> cases u <;> decide

theorem basis_cast {L : ℕ} (j : BasisLabel L) (x : PairBits L) :
    (basisInt j x : ℚ) = basisEntry j x := by simp only [basisInt,Int.cast_prod,digit_cast,basisEntry]

private theorem bit_cast {x : ℚ} (hx : Binary x) : (bitInt x : ℚ) = x := by
  rcases hx with rfl | rfl <;> norm_num [bitInt]

theorem channel_cast {L : ℕ} (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (h : Fin 3) (a b : Block L) : (channelInt w h a b : ℚ) = channel w h a b := by
  simp only [channelInt,channel,Int.cast_mul,Int.cast_prod,fun k => bit_cast (hw k)]

theorem residual_cast (K L : ℕ) (j : BasisLabel L) :
    (residualInt K L j : ℚ) = (D L : ℚ) * (windowExpansion K L).diagonal j := by
  have h := Dyadic.widen (denominator_bits j) (residualNum (windowCoeff K L) (antisymmetric j).card)
  change (residualInt K L j : ℚ) / (2:ℚ)^L = (windowExpansion K L).diagonal j at h
  simpa [D,mul_comm] using (div_eq_iff (by positivity : (2:ℚ)^L ≠ 0)).mp h

end VWZClique.TraceDyadic
end

/- TraceDyadic -/
section
namespace VWZClique.TraceDyadic
open UniformFolds Double

variable {L : ℕ}

theorem left_cast (S T : Finset (BasisLabel L)) (K J : ℕ) (w : ChannelKey L → ℚ)
    (hw : ∀ k, Binary (w k)) (u : Node S) (v : Node T) :
    (leftTable S T K J w u v : ℚ) = (D L : ℚ)^2 *
      leftEntry S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w u v := by
  simp only [leftTable,rawLeft,transform,Int.cast_mul,Int.cast_sum,residual_cast,basis_cast,
    channel_cast w hw,leftEntry,Rat.cast_id]
  ring

theorem mid_cast (T : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (v : Node T) (c : Block L) : (midTable T w v c : ℚ) = midEntry T w v c := by
  simp only [midTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,midEntry,Rat.cast_id]

theorem right_cast (S : Finset (BasisLabel L)) (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k))
    (c : Block L) (u : Node S) : (rightTable S w c u : ℚ) = rightEntry S w c u := by
  simp only [rightTable,transform,Int.cast_sum,Int.cast_mul,basis_cast,channel_cast w hw,rightEntry,Rat.cast_id]

theorem numerator_exact (S T : Finset (BasisLabel L)) (K J : ℕ)
    (w : ChannelKey L → ℚ) (hw : ∀ k, Binary (w k)) :
    (numerator S T K J w : ℚ) = (D L : ℚ)^2 *
      doubleProjection S T (windowExpansion K L).diagonal (windowExpansion J L).diagonal w := by
  rw [Double.trace_identity]
  change ((∑ u : Node S, ∑ v : Node T, leftTable S T K J w u v *
    (∑ c : Block L, midTable T w v c * rightTable S w c u) : ℤ) : ℚ) = _
  simp only [Int.cast_sum,Int.cast_mul,left_cast S T K J w hw,mid_cast T w hw,right_cast S w hw]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_assoc _ _ _

end VWZClique.TraceDyadic
end

/- CliqueQuotient -/
section
/-! Exact integer division by repeated addition, comparison and subtraction, for
    recovering scaled matrix-product entries on a RAM without a divide instruction.
    This is the arithmetic schedule; the cost below counts its scalar iterations. -/

namespace VWZClique.Quotient

@[simp] theorem twice_eq (j x : ℕ) : twice j x = 2^j*x := by
  induction j generalizing x with
  | zero => simp [twice]
  | succ j ih => rw [twice,ih,pow_succ]; ring

theorem scan_correct (h a d : ℕ) (_hd : 0 < d) (ha : a < 2^h*d) :
    a = (scan h a d).1*d + (scan h a d).2 ∧ (scan h a d).2 < d := by
  induction h generalizing a with
  | zero => simpa [scan] using ha
  | succ h ih =>
    rw [pow_succ] at ha
    have htop : 2^h*2*d = 2^h*d + 2^h*d := by ring
    rw [htop] at ha
    by_cases hy : 2^h*d ≤ a
    · have hsmall : a-2^h*d < 2^h*d := by omega
      obtain ⟨he,hr⟩ := ih (a-2^h*d) hsmall
      simp only [scan,twice_eq,if_pos hy,mul_one,add_mul]
      exact ⟨by omega,hr⟩
    · simpa only [scan,twice_eq,if_neg hy] using ih a (Nat.lt_of_not_ge hy)

theorem scan_quotient (h a d : ℕ) (hd : 0 < d) (ha : a < 2^h*d) :
    (scan h a d).1 = a/d ∧ (scan h a d).2 = a%d := by
  obtain ⟨he,hr⟩ := scan_correct h a d hd ha
  constructor
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero]
  · conv_rhs => rw [he, Nat.mul_comm (scan h a d).1 d, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem height_cover (a p : ℕ) : a < 2^(height a p)*(p+1) := by
  induction p using height.induct a with
  | case1 p hp ih =>
    rw [height,if_pos hp,pow_add]
    norm_num
    calc
      _ < 2^height a (p+p+1)*(p+p+1+1) := ih
      _ = _ := by ring
  | case2 p hp => rw [height,if_neg hp]; simpa using Nat.lt_of_not_ge hp

theorem quotient_correct (a d : ℕ) (hd : 0 < d) :
    (quotient a d).1 = a/d ∧ (quotient a d).2 = a%d := by
  apply scan_quotient _ _ _ hd
  have h := height_cover a 0
  simp only [zero_add,mul_one] at h
  exact h.trans_le (Nat.le_mul_of_pos_right _ hd)

theorem signed_exact (z : ℤ) (d : ℕ) (hd : 0 < d) : signed (z*d) d = z := by
  unfold signed
  rw [(quotient_correct _ _ hd).1, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel _ hd]
  have hs : (d:ℤ).sign = 1 := Int.sign_eq_one_of_pos (by exact_mod_cast hd)
  rw [Int.sign_mul, hs, mul_one, Int.sign_mul_natAbs]

end VWZClique.Quotient
end

/- UniformFoldIntegers -/
section
open VWZClique VWZClique.RankSwap VWZClique.WeightedProof
namespace VWZClique.UniformFolds

private theorem cutoff_le {K : ℕ} (hK : 4<K) (L : ℕ) :
    lower K L ≤ L ∧ width K L ≤ L := by
  have cut (j : ℕ) (hj : j ≤ 4*K) : j*L/(4*K) ≤ L :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right L hj)
  exact ⟨cut _ (by omega),(Nat.sub_le _ _).trans (cut _ (by omega))⟩

/-- The same coefficients used by the evaluator have O(L)-bit signed numerators
and a binary denominator exponent at most L. -/
theorem windowWordBounds {K : ℕ} (hK : 4<K) (L : ℕ) :
    (∀ i : (windowExpansion K L).Index, |(windowExpansion K L).coefficients i| ≤ (2:ℤ)^(3*L)) ∧
    ∀ j : BasisLabel L, ∃ e : ℕ, e ≤ L ∧ ∃ z : ℤ, |z| ≤ (2:ℤ)^(5*L+1) ∧
      (windowExpansion K L).diagonal j = Dyadic.value e z := by
  obtain ⟨hl,hw⟩ := cutoff_le hK L
  obtain ⟨coeff,diag⟩ := windowExpansion_coefficients K L
  have hs : (2:ℝ)^(lower K L)*4^(width K L) ≤ 2^(3*L) := by
    rw [show (4:ℝ) = 2^2 by norm_num,←pow_mul,←pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have ht : (3:ℝ)^L ≤ 2^(2*L) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have htotal : 1+(3:ℝ)^L*(2^(lower K L)*4^(width K L)) ≤ 2^(5*L+1) := by
    calc
      _ ≤ 1+(2:ℝ)^(2*L)*2^(3*L) := by gcongr
      _ = 1+2^(5*L) := by rw [←pow_add,show 2*L+3*L=5*L by omega]
      _ ≤ (2:ℝ)^(5*L+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=5*L)]
  refine ⟨fun i => ?_,fun j => ?_⟩
  · exact_mod_cast (coeff i).trans hs
  · obtain ⟨e,he,z,hz,v⟩ := diag j
    exact ⟨e,he,z,by exact_mod_cast hz.trans htotal,v⟩

/-- This coarse bound holds even at lengths below the asymptotic rank cutoff. -/
theorem windowTerms_le (K L : ℕ) : Fintype.card (windowExpansion K L).Index ≤ 2^(3*L) := by
  change Fintype.card (Terms L (width K L)) ≤ _
  rw [terms_card]
  calc
    _ ≤ ∑ S : Finset (Fin L), 4^S.card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 5^L := by
      simpa only [one_pow,mul_one,Fintype.card_fin] using
        (Fintype.sum_pow_mul_eq_add_pow (Fin L) (4:ℕ) 1)
    _ ≤ _ := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) L

private theorem subtotal {I : Type*} [Fintype I] (s : Finset I) (f : I → ℤ)
    (m v : ℕ) (hm : Fintype.card I ≤ 2^m) (hv : ∀ i, |f i| ≤ (2:ℤ)^v) :
    |∑ i ∈ s, f i| ≤ (2:ℤ)^(m+v) := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ s, (2:ℤ)^v := Finset.sum_le_sum fun i _ => hv i
    _ = (s.card:ℤ)*(2:ℤ)^v := by simp
    _ ≤ (2:ℤ)^m * 2^v := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_univ s).trans hm) (by positivity)
    _ = _ := (pow_add _ _ _).symm

/-- Every partial one-mask sum in an evaluation on binary inputs has at most
15L bits above the unit, independently of the enumeration order. -/
theorem singleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset (windowExpansion K L).Index) (v : (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i * v i| ≤ (2:ℤ)^(15*L) := by
  have hh := (windowWordBounds hK L).1
  rw [show 15*L = 3*L+(3*L+9*L) by omega]
  apply subtotal _ _ _ _ (windowTerms_le K L)
  intro i
  rw [abs_mul,pow_add]
  exact mul_le_mul (hh i) (hv i) (abs_nonneg _) (by positivity)

/-- Arbitrary partial sums of the two-mask branch fit a signed integer
with 21L bits above the unit. -/
theorem doubleSubtotal {K : ℕ} (hK : 4<K) (L : ℕ)
    (s : Finset ((windowExpansion K L).Index × (windowExpansion K L).Index))
    (v : (windowExpansion K L).Index × (windowExpansion K L).Index → ℤ)
    (hv : ∀ i, |v i| ≤ (2:ℤ)^(9*L)) :
    |∑ i ∈ s, (windowExpansion K L).coefficients i.1 *
      (windowExpansion K L).coefficients i.2 * v i| ≤ (2:ℤ)^(21*L) := by
  have hh := (windowWordBounds hK L).1
  have hm := windowTerms_le K L
  rw [show 21*L = (3*L+3*L) + ((3*L+3*L)+9*L) by omega]
  apply subtotal
  · rw [Fintype.card_prod,pow_add]
    exact Nat.mul_le_mul hm hm
  · intro i
    rw [abs_mul,abs_mul,pow_add,pow_add]
    exact mul_le_mul (mul_le_mul (hh i.1) (hh i.2) (abs_nonneg _) (by positivity))
      (hv i) (abs_nonneg _) (by positivity)

private theorem folded_integer {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) (d : Branch)
    (a b : Option (Mask L)) (ha : a.isSome = first d) (hb : b.isSome = second d) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(9*L) ∧
      placedFold (slots π H) a b ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  let r : Round L := ⟨H,π,a,b⟩
  have binary (i) : Binary (r.apply w i) := updated_binary _ _ _ _
    (r.inputs_property w Binary (Or.inr rfl) hw) i
  obtain ⟨z,hz,hv⟩ := binary_sum (child (slots π H) d) _ binary
  refine ⟨z,?_,?_⟩
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hz
    exact_mod_cast hz
  · exact (r.exact_value w d ha hb).symm.trans (by simpa only [Int.cast_natCast] using hv)

/-- The complete projected contribution is integral on every Boolean fold input,
even though its three channel matrices contain rational diagonal coefficients. -/
theorem traceProjection_integer {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    ∃ z : ℤ, |z| ≤ (2:ℤ)^(21*L+2) ∧
      traceProjection L (windowExpansion K L) ((Round.mk H π none none).inputs w) = (z:ℚ) := by
  classical
  let q := windowExpansion K L
  let E := slots π H
  let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
  choose left leftBound leftVal using
    fun i : q.Index => folded_integer H π w hw .left (some (q.masks i)) none rfl rfl
  choose right rightBound rightVal using
    fun j : q.Index => folded_integer H π w hw .right none (some (q.masks j)) rfl rfl
  choose both bothBound bothVal using fun ij : q.Index × q.Index =>
    folded_integer H π w hw .both (some (q.masks ij.1)) (some (q.masks ij.2)) rfl rfl
  let A : ℤ := ∑ i, q.coefficients i * left i
  let B : ℤ := ∑ j, q.coefficients j * right j
  let D : ℤ := ∑ ij : q.Index × q.Index, (q.coefficients ij.1 * q.coefficients ij.2) * both ij
  have ha : |A| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ left leftBound
  have hb : |B| ≤ (2:ℤ)^(15*L) := singleSubtotal hK L Finset.univ right rightBound
  have hd : |D| ≤ (2:ℤ)^(21*L) := doubleSubtotal hK L Finset.univ both bothBound
  have la : ∑ i, (q.coefficients i:ℚ)*placedFold E (some (q.masks i)) none u = (A:ℚ) := by
    simp only [A,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg _ (leftVal i))
  have lb : ∑ j, (q.coefficients j:ℚ)*placedFold E none (some (q.masks j)) u = (B:ℚ) := by
    simp only [B,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl (fun j _ => congrArg _ (rightVal j))
  have ld : ∑ i, ∑ j, ((q.coefficients i:ℚ)*(q.coefficients j:ℚ))*
      placedFold E (some (q.masks i)) (some (q.masks j)) u = (D:ℚ) := by
    simp only [D,Int.cast_sum,Int.cast_mul,Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => congrArg _ (bothVal (i,j))))
  obtain ⟨v,hv,value⟩ := binary_sum H w hw
  have hval : placedFold E none none u = (v:ℚ) := (input_exact π H w).trans value
  have h := q.decompose E u (input_supported (Round.mk H π none none) w)
  rw [la,lb,ld,hval] at h
  let P : ℤ := (2:ℤ)^(21*L)
  have h15 : (2:ℤ)^(15*L) ≤ P := pow_le_pow_right₀ (by norm_num) (by omega)
  have hv' : |(v:ℤ)| ≤ P := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [←pow_mul,Nat.mul_comm L 9] at hv
    exact (by exact_mod_cast hv : (v:ℤ) ≤ 2^(9*L)).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine ⟨(v:ℤ)-A-B+D,?_,?_⟩
  · calc
      _ ≤ |(v:ℤ)-A-B|+|D| := abs_add_le _ _
      _ ≤ (|(v:ℤ)-A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ (|(v:ℤ)|+|A|+|B|)+|D| := by gcongr; exact abs_sub _ _
      _ ≤ P+P+P+P := add_le_add (add_le_add (add_le_add hv' (ha.trans h15)) (hb.trans h15)) hd
      _ = _ := by rw [pow_add]; dsimp [P]; ring
  · rw [traceProjection_correct]
    push_cast
    linarith

/-- On every actual graph call the integer trace numerator is divisible by the
common binary denominator. The signed shift/subtract quotient returns exactly the
projected contribution. -/
theorem traceIntegerQuotient {K : ℕ} (hK : 4<K) (L : ℕ)
    (H : SimpleGraph V) (π : Equiv.Perm V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) :
    let q := windowExpansion K L
    let u := (Round.mk H π (none : Option (Mask L)) none).inputs w
    let z := TraceDyadic.numerator q.labels q.labels K K u
    let d : ℕ := (2^L)^2
    (d:ℤ) ∣ z ∧ (Quotient.signed z d:ℚ) = traceProjection L q u ∧
      |Quotient.signed z d| ≤ (2:ℤ)^(21*L+2) := by
  intro q u z d
  obtain ⟨v,hv,he⟩ := traceProjection_integer hK L H π w hw
  have hb (i) : Binary (u i) :=
    (Round.mk H π (none : Option (Mask L)) none).inputs_property w Binary (Or.inr rfl) hw i
  have hx := TraceDyadic.numerator_exact q.labels q.labels K K u hb
  have he' : doubleProjection q.labels q.labels q.diagonal q.diagonal u = (v:ℚ) :=
    (traceProjection_correct q u).symm.trans he
  have eq : z = v*(d:ℤ) := by
    have h : (z:ℚ) = ((v*(d:ℤ):ℤ):ℚ) := by
      rw [show (z:ℚ) = (TraceDyadic.D L : ℚ)^2 *
        doubleProjection q.labels q.labels q.diagonal q.diagonal u from hx,he']
      simp [d,TraceDyadic.D,mul_comm]
    exact_mod_cast h
  have hd : 0<d := by dsimp [d]; positivity
  have res : Quotient.signed z d = v := by rw [eq,Quotient.signed_exact _ _ hd]
  exact ⟨⟨v,eq.trans (mul_comm _ _)⟩,res ▸ he.symm,res ▸ hv⟩

end VWZClique.UniformFolds
end

/- IntegerFoldEvaluation -/
section
open VWZClique VWZClique.SparseProof
namespace VWZClique.UniformFolds

theorem integerPlan_cast (L : ℕ) {H : SimpleGraph V} (p : Plan H)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    (integerPlan L p w:ℚ) =
      evaluatePlan (fun H => windowExpansion (windowAt (Nat.card H.edgeSet)) L)
        (sparseLeaf L) (traceProjection L) p w := by
  induction p generalizing w with
  | leaf H hh => exact integerLeaf_cast L H hh w hw
  | split H π hp kids ih =>
    let K := windowAt (Nat.card H.edgeSet)
    let q := windowExpansion K L
    have htrace : (integerTrace K L H π w:ℚ) =
        traceProjection L q ((Round.mk H π none none).inputs w) :=
      (traceIntegerQuotient (cutoffTable_spec H).2.2.1 L H π w hw).2.1
    have hcall (d : Branch) (a b : Option (Mask L)) :
        (integerPlan L (kids d) ((Round.mk H π a b).apply w):ℚ) =
        evaluatePlan (fun G => windowExpansion (windowAt (Nat.card G.edgeSet)) L)
          (sparseLeaf L) (traceProjection L) (kids d) ((Round.mk H π a b).apply w) :=
      let r := Round.mk H π a b
      ih d (r.apply w) (updated_binary _ _ _ _ (r.inputs_property w Binary (Or.inr rfl) hw))
    simp only [integerPlan,evaluatePlan,Int.cast_add,Int.cast_sub,Int.cast_sum,Int.cast_mul]
    rw [htrace]
    simp_rw [hcall]
    rfl

theorem integerPlan_exact (L : ℕ) {H : SimpleGraph V} (p : Plan H) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) : (integerPlan L p w:ℚ) = weightedSum H w :=
  (integerPlan_cast L p w hw).trans
    (evaluatePlan_correct _ _ _ (sparseLeaf_correct L) traceProjection_correct _ _)

/-- Apply the fixed plan to binary graph weights with an integer result. -/
theorem integerPlan_correct (L : ℕ) (H : SimpleGraph V) (w : WeightKey (2^L) → ℚ)
    (hw : ∀ k, Binary (w k)) : (integerPlan L (fixed H) w:ℚ) = weightedSum H w :=
  integerPlan_exact L (fixed H) w hw

end VWZClique.UniformFolds
end

/- MaskEnumeration -/
section
open VWZClique
namespace VWZClique.RankSwap.MaskEnumeration

theorem scan_range_bound (L : ℕ) : 5^L ≤ (2^L)^3 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (by decide) L

end VWZClique.RankSwap.MaskEnumeration
end

/- NativeFoldTraversal -/
section
namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured

instance phaseFinite (I : Type) [Fintype I] (d : Branch) : Fintype (phaseIndex I d) := by
  cases d <;> dsimp [phaseIndex] <;> infer_instance

noncomputable def phaseValue {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V) (d : Branch)
    (childPlan : Plan (child (WeightedProof.slots π H) d)) (w : WeightKey (2^L) → ℚ)
    (i : Fin (visits (Fintype.card (qOf H L).Index) d)) : ℤ :=
  let c := numbered H d i
  c.coeff * integerPlan L childPlan (childWeights H π c w)

theorem split_eq {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V) (hp)
    (kids : (d : Branch) → Plan (child (WeightedProof.slots π H) d)) (w : WeightKey (2^L) → ℚ) :
    integerPlan L (.split H π hp kids) w =
        integerTrace (windowAt (Nat.card H.edgeSet)) L H π w +
        (∑ i, phaseValue H π .left (kids .left) w i) +
        (∑ i, phaseValue H π .right (kids .right) w i) +
        (∑ i, phaseValue H π .both (kids .both) w i) := by
  let f (d : Branch) (i : phaseIndex (qOf H L).Index d) :=
    let c := callSpec (qOf H L) d i
    c.coeff * integerPlan L (kids d) (childWeights H π c w)
  have reorder (d : Branch) : (∑ i, phaseValue H π d (kids d) w i) = ∑ i, f d i :=
    (phaseOrder H d).sum_comp (f d)
  have pairs : (∑ i, f .both i) = ∑ i, ∑ j, f .both (i,j) := by
    change (∑ ij : (qOf H L).Index × (qOf H L).Index, f .both ij) = _
    rw [Fintype.sum_prod_type]
  rw [reorder,reorder,reorder,pairs]
  simp [integerPlan,f,qOf,callSpec,childWeights,Finset.sum_neg_distrib,sub_eq_add_neg] <;>
    first | rfl | congr! 20 <;> first | rfl | exact Subsingleton.elim _ _

/-- All commands are independent of the input length. Depth and pattern are static. -/
structure Operations where
  leaf : ℕ → SimpleGraph V → Command
  project : ℕ → SimpleGraph V → Equiv.Perm V → Command
  reset : ℕ → Branch → Command
  push : ℕ → SimpleGraph V → Equiv.Perm V → Branch → Command
  pop : ℕ → SimpleGraph V → Branch → Command
  test : ℕ → ℤ
  finish : ℕ → Command

def stage (o : Operations) (depth : ℕ) (H : SimpleGraph V) (π : Equiv.Perm V)
    (d : Branch) (kid : Command) : Command :=
  .repeatWhileNegative (.seq (o.push depth H π d) (.seq kid (o.pop depth H d))) (o.test depth)

noncomputable def emitPlan (o : Operations) : {H : SimpleGraph V} → Plan H → ℕ → Command
  | _,.leaf H _,depth => o.leaf depth H
  | _,.split H π _ kids,depth =>
    let call (d : Branch) := stage o depth H π d (emitPlan o (kids d) (depth+1))
    .seq (o.project depth H π) (.seq (call .left)
      (.seq (o.reset depth .right) (.seq (call .right)
      (.seq (o.reset depth .both) (.seq (call .both) (o.finish depth))))))

theorem Transition.seq {L W} {repr : List (Slot L) → Memory → Prop} {a b s t u A B}
    (ha : Transition W repr a s t A) (hb : Transition W repr b t u B) :
    Transition W repr (.seq a b) s u (A+B) := by
  intro m h
  obtain ⟨i,hi,x,rx,hx⟩ := ha _ h
  obtain ⟨j,hj,y,ry,hy⟩ := hb _ hx
  exact ⟨_,Nat.add_le_add hi hj,y,.seq rx ry,hy⟩

/-- If a stage's body advances its cursor, accumulates its signed term, and sets
the continuation flag, the one native backward branch visits every term once. -/
theorem stage_loop {W L count bound : ℕ} (hc : 0<count) (repr : List (Slot L) → Memory → Prop)
    (body : Command) (test : ℤ) {depth : ℕ} {H : SimpleGraph V} {π : Equiv.Perm V} {d : Branch} (w : WeightKey (2^L) → ℚ) (stack : List (Slot L))
    (v : Fin count → ℤ)
    (step : ∀ (i : Fin count) z m, repr (.cursor depth H π d w i z :: stack) m →
      ∃ f ≤ bound, ∃ x, Runs W body m f x ∧ repr (.cursor depth H π d w (i.val+1) (z+v i) :: stack) x ∧
        Fits W (x test) ∧ (x test<0 ↔ i.val+1<count)) (z : ℤ) :
    Transition W repr (.repeatWhileNegative body test) (.cursor depth H π d w 0 z :: stack)
      (.cursor depth H π d w count (z+∑ i,v i) :: stack) (count*(bound+1)) := by
  let sum (k : ℕ) := ∑ j ∈ Finset.range k, (if hj : j<count then v ⟨j,hj⟩ else 0)
  have add (i : Fin count) : sum (i.val+1)=sum i.val+v i := by simp [sum,Finset.sum_range_succ,i.isLt]
  have aux (r k : ℕ) (eqn : k+r=count) (hr : 0<r) (m : Memory)
      (hm : repr (.cursor depth H π d w k (z+sum k) :: stack) m) :
      ∃ f ≤ r*(bound+1), ∃ x, Runs W (.repeatWhileNegative body test) m f x ∧
        repr (.cursor depth H π d w count (z+sum count) :: stack) x := by
    induction r generalizing k m with
    | zero => omega
    | succ r ih =>
      let i : Fin count := ⟨k,by omega⟩
      obtain ⟨f,hf,x,run,xh,fit,flag⟩ := step i _ m hm
      have hnext : repr (.cursor depth H π d w (k+1) (z+sum (k+1)) :: stack) x := by
        simpa only [show k+1=i.val+1 from rfl,add i,← add_assoc] using xh
      by_cases he : r=0
      · subst r
        have last : k+1=count := by omega
        exact ⟨_,by omega,x,.loop_done run fit (by rw [flag]; exact Nat.not_lt.mpr last.ge),
          last ▸ hnext⟩
      · obtain ⟨g,hg,y,rest,last⟩ := ih (k+1) (by omega) (by omega) x hnext
        exact ⟨_,by rw [Nat.succ_mul]; omega,y,.loop_again run fit (flag.mpr (by change k+1<count; omega)) rest,last⟩
  have total : sum count = ∑ i,v i := by
    dsimp [sum]
    rw [← Fin.sum_univ_eq_sum_range]
    simp
  intro m hm
  rw [← total]
  exact aux count 0 (by omega) hc m (by simpa [sum] using hm)

end VWZClique.NativeTraversal
end

/- NativeFoldProgram -/
section
namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured
open WeightedProof

private theorem number_pos (L : ℕ) (H : SimpleGraph V) : 0<number L H := by
  change 0 < Fintype.card (RankSwap.Terms L _)
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨∅,?_⟩,fun i => ⟨0,?_⟩⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩
  · simp [RankSwap.choices,RankSwap.active]

private theorem visits_pos {m : ℕ} (hm : 0 < m) (d : Branch) : 0<visits m d := by
  cases d <;> simp [visits,hm]

noncomputable def cost (L : ℕ) (c : Charges) : {H : SimpleGraph V} → Plan H → ℕ
  | _,.leaf H _ => c.small H
  | _,.split H _ _ kids =>
    let phase d := visits (number L H) d * ((c.push H + (cost L c (kids d)+c.pop))+1)
    c.projection H + (phase .left + (c.reset+(phase .right+(c.reset+(phase .both+c.finish)))))

/-- Each hypothesis concerns one nonrecursive kernel. The inductive compiler
builds all nested loops and establishes their total running time. -/
structure Correct {L : ℕ} (o : Operations) (W : ℕ) (repr : List (Slot L) → Memory → Prop) (c : Charges) : Prop where
  leaf : ∀ depth H hh w stack, depth+Nat.card (SimpleGraph.edgeSet H) ≤ 36 → (∀ i, Binary (w i)) →
    Transition W repr (o.leaf depth H) (.input depth w::stack) (.value depth (integerLeaf L H hh w)::stack) (c.small H)
  project : ∀ depth H π w stack, depth+Nat.card (SimpleGraph.edgeSet H) ≤ 36 → (∀ i, Binary (w i)) →
    Transition W repr (o.project depth H π) (.input depth w::stack)
      (.cursor depth H π .left w 0 (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::stack) (c.projection H)
  reset : ∀ depth H π d e w i z stack, depth ≤ 36 →
    Transition W repr (o.reset depth e) (.cursor depth H π d w i z::stack) (.cursor depth H π e w 0 z::stack) c.reset
  finish : ∀ depth H π d w i z stack, depth ≤ 36 →
    Transition W repr (o.finish depth) (.cursor depth H π d w i z::stack) (.value depth z::stack) c.finish
  push : ∀ depth H π d (i : Fin (visits (number L H) d)) w z stack, depth<36 → (∀ j, Binary (w j)) →
    Transition W repr (o.push depth H π d) (.cursor depth H π d w i.val z::stack)
      (.input (depth+1) (childWeights H π (numbered H d i) w):: .cursor depth H π d w i.val z::stack) (c.push H)
  pop : ∀ depth H π d (i : Fin (visits (number L H) d)) w z childValue stack m, depth<36 →
    repr (.value (depth+1) childValue :: .cursor depth H π d w i.val z :: stack) m →
    ∃ f ≤ c.pop, ∃ x, Runs W (o.pop depth H d) m f x ∧
      repr (.cursor depth H π d w (i.val+1) (z+(numbered H d i).coeff*childValue)::stack) x ∧
      Fits W (x (o.test depth)) ∧ (x (o.test depth)<0 ↔ i.val+1<visits (number L H) d)

theorem compiled_correct {L W : ℕ} (o : Operations) (repr : List (Slot L) → Memory → Prop)
    (c : Charges) (spec : Correct o W repr c) {H : SimpleGraph V} (p : Plan H) (depth : ℕ)
    (hd : depth + Nat.card H.edgeSet ≤ 36) (w : WeightKey (2^L) → ℚ) (hw : ∀ i, Binary (w i)) (stack : List (Slot L)) :
    Transition W repr (emitPlan o p depth) (.input depth w :: stack)
      (.value depth (integerPlan L p w) :: stack) (cost L c p) := by
  induction p generalizing depth w stack with
  | leaf H hh => exact spec.leaf depth H hh w stack hd hw
  | split H π hp kids ih =>
    have deep (d : Branch) : depth+1+Nat.card (child (slots π H) d).edgeSet ≤ 36 := by
      have := branch_smaller H π hp d
      omega
    have ds : depth<36 := by have := deep .left; omega
    let run (d : Branch) := stage o depth H π d (emitPlan o (kids d) (depth+1))
    let val (d : Branch) := phaseValue H π d (kids d) w
    let m := number L H
    let B (d : Branch) := visits m d*((c.push H+(cost L c (kids d)+c.pop))+1)
    have phase (d : Branch) (acc : ℤ) : Transition W repr (run d) (.cursor depth H π d w 0 acc :: stack)
        (.cursor depth H π d w (visits m d) (acc+∑ i,val d i) :: stack) (B d) := by
      apply stage_loop (visits_pos (number_pos L H) d)
      intro i z x init
      let j := numbered H d i
      let childW := childWeights H π j w
      obtain ⟨t,ht,y,prep,ready⟩ := spec.push depth H π d i w z stack ds hw x init
      have hchild : ∀ k, Binary (childW k) :=
        updated_binary (WeightedProof.slots π H) j.a j.b _ ((Round.mk H π j.a j.b).inputs_property w Binary (Or.inr rfl) hw)
      obtain ⟨u,hu,v,sub,done⟩ := ih d (depth+1) (deep d) childW hchild (.cursor depth H π d w i.val z::stack) y ready
      obtain ⟨s,hs,last,post,hd,fit,flag⟩ := spec.pop depth H π d i w z _ stack v ds done
      exact ⟨_,Nat.add_le_add ht (Nat.add_le_add hu hs),last,.seq prep (.seq sub post),hd,fit,flag⟩
    let z₀ := integerTrace (windowAt (Nat.card H.edgeSet)) L H π w
    have h := (spec.project depth H π w stack hd hw).seq <| (phase .left z₀).seq <|
      (spec.reset depth H π .left .right _ _ _ stack ds.le).seq <| (phase .right _).seq <|
      (spec.reset depth H π .right .both _ _ _ stack ds.le).seq <| (phase .both _).seq <| spec.finish depth H π .both _ _ _ stack ds.le
    rw [split_eq]
    exact h

end VWZClique.NativeTraversal
end

/- CliqueWord -/
section
/-! Word-level facts for the published RAM representation of clique counting. -/

namespace VWZClique.BlockReduction

open Classical
open TrulySubcubicAPSP

/-- Signed words of the target's width represent every nonnegative value at most `n^k`. -/
theorem word_exact {n k a : ℕ} (hn : 1 ≤ n) (ha : a ≤ n^k) :
    (BitVec.ofInt ((k+2)*(n.log2+1)) (a:ℤ)).toInt = (a:ℤ) := by
  let L := n.log2 + 1
  have hbase : n < 2^L := (Nat.log2_lt (by omega : n ≠ 0)).mp (by simp [L])
  have hlo : n^k ≤ 2^(L*k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hbase.le _
  have hw : L*k < (k+2)*L-1 := by
    have hL : 0 < L := Nat.succ_pos _
    have hm : (k+2)*L = L*k + L + L := by ring
    omega
  have hlt := ha.trans_lt (hlo.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hw))
  apply BitVec.toInt_ofInt_eq_self (by positivity) (by exact le_trans (by norm_num : -(2:ℤ)^(_ : ℕ) ≤ 0) (by positivity))
  exact_mod_cast hlt

/-- The row-major representation is the ordinary length-`n²` listing. -/
theorem rowByRow_eq_ofFn {n : ℕ} (A : Fin n → Fin n → ℤ) :
    rowByRow A = List.ofFn (fun z : Fin (n*n) =>
      A (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold rowByRow
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he (h : (i:ℕ)*n+j < n*n) : (⟨(i:ℕ)*n+j,h⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change (i:ℕ)*n+j = (j:ℕ)+n*i
    ring
  simp only [he, Equiv.symm_apply_apply]

theorem graphInput_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (MonDepMW.graphInput G).length = 1+n*n := by
  classical
  simp [MonDepMW.graphInput, rowByRow_eq_ofFn, Nat.add_comm]

/-- Reading an input graph at a row-major index retrieves the adjacency bit. -/
theorem graphInput_getD {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (MonDepMW.graphInput G).getD (1 + (i:ℕ)*n + j) 0 = if G.Adj i j then 1 else 0 := by
  classical
  have h : (i:ℕ)*n+j < n*n := by
    calc
      _ < (i:ℕ)*n+n := Nat.add_lt_add_left j.isLt _
      _ = ((i:ℕ)+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right _ i.isLt
  have he : (⟨(i:ℕ)*n+j,h⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change (i:ℕ)*n+j = (j:ℕ)+n*i
    ring
  rw [show 1+(i:ℕ)*n+j = ((i:ℕ)*n+j)+1 by omega]
  change (rowByRow _).getD ((i:ℕ)*n+j) 0 = _
  rw [rowByRow_eq_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
  simp only [List.getElem_ofFn, he, Equiv.symm_apply_apply]

end VWZClique.BlockReduction
end

/- CliqueReduction -/
section
/-! Exact reduction from unordered cliques to a single weighted nine-vertex instance.
    A fixed vertex fills unused slots, and order constraints choose one increasing
    enumeration of each clique. The extra slots allow all clique sizes. -/

namespace VWZClique
namespace BlockReduction

open Finset
open scoped BigOperators
noncomputable section
open Classical

/-- An increasing enumeration of a clique. -/
def Ordered {n k : ℕ} (G : SimpleGraph (Fin n)) (f : Fin k → Fin n) : Prop :=
  ∀ i j, i < j → f i < f j ∧ G.Adj (f i) (f j)

/-- A clique has exactly one increasing enumeration. -/
theorem card_ordered {n k : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter fun f : Fin k → Fin n => Ordered G f).card = count G k := by
  classical
  unfold count
  apply Finset.card_bij (fun f _ => univ.image f)
  · intro f hf
    have hg : Ordered G f := (mem_filter.mp hf).2
    have hmono : StrictMono f := fun i j h => (hg i j h).1
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩, ?_⟩
    · simpa using card_image_of_injective univ hmono.injective
    · intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      rcases lt_trichotomy i j with hij | hij | hij
      · exact (hg i j hij).2
      · exact (huv (congrArg f hij)).elim
      · exact (hg j i hij).2.symm
  · intro f hf g hg hfg
    have hm : StrictMono f := fun i j h => ((mem_filter.mp hf).2 i j h).1
    have hn : StrictMono g := fun i j h => ((mem_filter.mp hg).2 i j h).1
    have hcard : (univ.image f).card = k := by
      simpa using card_image_of_injective univ hm.injective
    apply (orderEmbOfFin_unique hcard (fun x => mem_image.mpr ⟨x, mem_univ _, rfl⟩) hm).trans
    symm
    apply orderEmbOfFin_unique hcard _ hn
    intro x
    rw [hfg]
    exact mem_image.mpr ⟨x, mem_univ _, rfl⟩
  · intro s hs
    obtain ⟨hsize, hclique⟩ := mem_filter.mp hs
    have hcard := (mem_powersetCard.mp hsize).2
    let f := s.orderEmbOfFin hcard
    refine ⟨f, mem_filter.mpr ⟨mem_univ _, ?_⟩, s.image_orderEmbOfFin_univ hcard⟩
    intro i j hij
    have hlt := f.strictMono hij
    exact ⟨hlt, hclique _ (s.orderEmbOfFin_mem hcard _) _ (s.orderEmbOfFin_mem hcard _) hlt.ne⟩

/-- Read the assignment at a padded slot. -/
def readSlot {n t : ℕ} (a : V → Fin (n^t)) (z : Fin (9*t)) : Fin n :=
  let ij := finProdFinEquiv.symm z
  digit (a ij.1) ij.2

@[simp]
theorem readSlot_slot {n t : ℕ} (a : V → Fin (n^t)) (i : V) (p : Fin t) :
    readSlot a (slot i p) = digit (a i) p := by simp [readSlot, slot]

/-- Assemble the nine block labels from a tuple, filling inactive slots by `pad`. -/
def pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) : V → Fin (n^t) :=
  fun i => finFunctionFinEquiv fun p =>
    if h : (slot i p).val < k then f ⟨(slot i p).val, h⟩ else pad

@[simp]
theorem readSlot_pack {n k t : ℕ} (pad : Fin n) (f : Fin k → Fin n) (z : Fin (9*t)) :
    readSlot (pack (t := t) pad f) z = if h : z.val < k then f ⟨z.val, h⟩ else pad := by
  obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective z
  change readSlot _ (slot i p) = _
  rw [readSlot_slot]
  simp [digit, pack, slot]

/-- Read the first `k` slots, discarding padding. -/
def unpack {n k t : ℕ} (h : k ≤ 9*t) (a : V → Fin (n^t)) : Fin k → Fin n :=
  fun z => readSlot a (Fin.castLE h z)

@[simp]
theorem unpack_pack {n k t : ℕ} (h : k ≤ 9*t) (pad : Fin n) (f : Fin k → Fin n) :
    unpack h (pack pad f) = f := by
  funext z
  simp [unpack, z.isLt]

theorem compatible_comm {n t k : ℕ} {G : SimpleGraph (Fin n)}
    {r s : Fin (9*t)} {u v : Fin n} :
    compatible G k r s u v ↔ compatible G k s r v u := by
  unfold compatible
  constructor <;> intro h h₁ h₂ <;> exact (h h₂ h₁).symm

def valid {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (pad : Fin n)
    (a : V → Fin (n^t)) : Prop :=
  (∀ i, unaryOK G k pad i (a i)) ∧
  ∀ i j, i < j → edgeOK G k i j (a i) (a j)

private theorem valid_iff_slots {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} :
    valid G k pad a ↔
      (∀ r, k ≤ r.val → readSlot a r = pad) ∧
      ∀ r s, compatible G k r s (readSlot a r) (readSlot a s) := by
  constructor
  · rintro ⟨hu, he⟩
    constructor
    · intro r
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      change k ≤ (slot i p).val → readSlot a (slot i p) = pad
      simpa only [readSlot_slot] using (hu i).1 p
    · intro r s
      obtain ⟨⟨i,p⟩, rfl⟩ := finProdFinEquiv.surjective r
      obtain ⟨⟨j,q⟩, rfl⟩ := finProdFinEquiv.surjective s
      change compatible _ _ (slot i p) (slot j q) (readSlot a (slot i p)) (readSlot a (slot j q))
      rw [readSlot_slot, readSlot_slot]
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact he i j hij p q
      · exact (hu i).2 p q
      · exact compatible_comm.mpr (he j i hji q p)
  · rintro ⟨hp, hc⟩
    constructor
    · intro i
      constructor
      · intro p
        simpa only [readSlot_slot] using hp (slot i p)
      · intro p q
        simpa only [readSlot_slot] using hc (slot i p) (slot i q)
    · intro i j _ p q
      simpa only [readSlot_slot] using hc (slot i p) (slot j q)

theorem pack_valid {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {f : Fin k → Fin n} (hf : Ordered G f) : valid (t := t) G k pad (pack pad f) := by
  apply valid_iff_slots.mpr
  constructor
  · intro r hr
    simp [readSlot_pack, Nat.not_lt.mpr hr]
  · intro r s hr hs
    rw [readSlot_pack, readSlot_pack, dif_pos hr, dif_pos hs]
    exact ⟨fun hij => hf _ _ hij, fun hji => hf _ _ hji⟩

theorem ordered_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) : Ordered G (unpack h a) := by
  intro i j hij
  exact (((valid_iff_slots.mp ha).2 (Fin.castLE h i) (Fin.castLE h j)) i.isLt j.isLt).1 hij

theorem pack_unpack {n k t : ℕ} {G : SimpleGraph (Fin n)} {pad : Fin n}
    {a : V → Fin (n^t)} (h : k ≤ 9*t) (ha : valid G k pad a) :
    pack pad (unpack h a) = a := by
  funext i
  apply finFunctionFinEquiv.symm.injective
  funext p
  change digit (pack pad (unpack h a) i) p = digit (a i) p
  rw [← readSlot_slot, ← readSlot_slot, readSlot_pack]
  split_ifs with hp
  · rfl
  · exact ((valid_iff_slots.mp ha).1 _ (Nat.le_of_not_gt hp)).symm

theorem weights_binary {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n))
    (k : ℕ) (pad : Fin n) (key : WeightKey (n^t)) :
    weights (F := F) G k pad key = 0 ∨ weights (F := F) G k pad key = 1 := by
  rcases key with ⟨i,a⟩ | ⟨i,j,a,b⟩ <;> simp [weights] <;> exact Classical.em _ |>.symm

/-- The weighted sum on nine vertices is the number of unordered `k`-cliques.
    Any block width with at least `k` slots works. -/
theorem weighted_eq_count {F : Type*} [Field F] {n k t : ℕ} (G : SimpleGraph (Fin n))
    (pad : Fin n) (h : k ≤ 9*t) :
    weightedSum (⊤ : SimpleGraph V) (weights (F := F) (t := t) G k pad) =
    (count G k : F) := by
  classical
  have hn : (univ.filter fun f : Fin k → Fin n => Ordered G f).card =
      (univ.filter fun a : V → Fin (n^t) => valid G k pad a).card := by
    apply Finset.card_bij (fun f _ => pack pad f)
    · intro f hf
      exact mem_filter.mpr ⟨mem_univ _, pack_valid (mem_filter.mp hf).2⟩
    · intro f _ g _ hfg
      simpa using congrArg (unpack h) hfg
    · intro a ha
      obtain hv := (mem_filter.mp ha).2
      exact ⟨unpack h a, mem_filter.mpr ⟨mem_univ _, ordered_unpack h hv⟩, pack_unpack h hv⟩
  rw [← card_ordered G, hn]
  unfold weightedSum
  calc
    _ = ∑ a : V → Fin (n^t), (if valid G k pad a then (1:F) else 0) := by
      apply sum_congr rfl
      intro a _
      by_cases hu : ∀ i, unaryOK G k pad i (a i)
      · have hones : (∏ i : V, weights (F := F) G k pad (.inl (i,a i))) = 1 :=
          prod_eq_one fun i _ => by simp [weights, hu i]
        rw [hones, one_mul]
        by_cases he : ∀ i j, i < j → edgeOK G k i j (a i) (a j)
        · rw [if_pos (show valid G k pad a from ⟨hu,he⟩)]
          apply prod_eq_one
          intro i _
          apply prod_eq_one
          intro j _
          by_cases hij : i < j
          · simp [hij, SimpleGraph.top_adj, hij.ne, weights, he i j hij]
          · simp [hij]
        · rw [if_neg (show ¬ valid G k pad a from fun hh => he hh.2)]
          obtain ⟨i,hi⟩ := not_forall.mp he
          obtain ⟨j,hj⟩ := not_forall.mp hi
          have hij : i < j := by by_contra h'; exact hj (fun h => (h' h).elim)
          have hbad : ¬ edgeOK G k i j (a i) (a j) := fun h => hj (fun _ => h)
          apply prod_eq_zero (mem_univ i)
          apply prod_eq_zero (mem_univ j)
          simp [hij, SimpleGraph.top_adj, hij.ne, weights, hbad]
      · rw [if_neg (show ¬ valid G k pad a from fun hh => hu hh.1)]
        obtain ⟨i,hi⟩ := not_forall.mp hu
        apply mul_eq_zero_of_left
        apply prod_eq_zero (mem_univ i)
        simp [weights, hi]
    _ = _ := Finset.sum_boole _ _

/-- The minimum common width accommodates every clique size. -/
theorem weighted_eq_count_ceil {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (k : ℕ) :
    weightedSum (⊤ : SimpleGraph V)
      (weights (F := F) (t := (k+8)/9) G k ⟨0,hn⟩) = (count G k : F) :=
  weighted_eq_count G _ (by omega)

end
end BlockReduction
end VWZClique
end

/- WordGraph -/
section
/-! Native row-major graph reads and grouped input tests for the clique word RAM. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical
open TrulySubcubicAPSP

/-- The two endpoints are ordinary vertex numbers. Cell zero holds the graph order. -/
def address {n : ℕ} (u v : Fin n) : ℤ := ((1+u.val*n+v.val : ℕ) : ℤ)

def GraphAt {n : ℕ} (G : SimpleGraph (Fin n)) (m : Memory) : Prop :=
  m 0 = (n:ℤ) ∧ ∀ u v, m (address u v) = if G.Adj u v then 1 else 0

theorem graphAt_input {n : ℕ} (G : SimpleGraph (Fin n)) :
    GraphAt G (input (MonDepMW.graphInput G)) := by
  classical
  refine ⟨?_,?_⟩
  · simp [input,MonDepMW.graphInput]
  · intro u v
    unfold input address
    rw [if_neg (Int.not_lt.mpr (Int.natCast_nonneg _)), Int.toNat_natCast]
    exact graphInput_getD G u v

/-- Within a test the scratch cells are -1 through -4. Every graph cell and every digit register
outside that interval survives a weight test. -/
def Protected (a : ℤ) : Prop := a ≤ -5 ∨ 0 ≤ a

def Frame (m out : Memory) : Prop := ∀ a, Protected a → out a = m a

theorem Frame.refl (m : Memory) : Frame m m := fun _ _ => rfl
theorem Frame.trans {a b c : Memory} (ab : Frame a b) (bc : Frame b c) : Frame a c :=
  fun i hi => (bc i hi).trans (ab i hi)

theorem Frame.write (m : Memory) {r : ℤ} (hr : -5 < r ∧ r < 0) (v : ℤ) :
    Frame m (update m r v) := by
  intro i hi
  have hd : i ≠ r := by rcases hi with h|h <;> omega
  simp [update,hd]

theorem GraphAt.frame {n : ℕ} {G : SimpleGraph (Fin n)} {m out : Memory}
    (h : GraphAt G m) (fr : Frame m out) : GraphAt G out := by
  refine ⟨(fr 0 (Or.inr le_rfl)).trans h.1,?_⟩
  intro u v
  exact (fr _ (Or.inr (Int.natCast_nonneg _))).trans (h.2 u v)

/-- Magnitude available to every indirect address and signed comparison
in these routines. Four times the binary input-order length suffices. -/
def Capacity (W n : ℕ) : Prop := (n:ℤ)^2 < (2:ℤ)^(W-1)

theorem graphCapacity {b n : ℕ} (hb : 4 ≤ b) (hn : 1 ≤ n) :
    Capacity (b*(n.log2+1)) n := by
  have h := BitVec.toInt_lt (x := BitVec.ofInt ((2+2)*(n.log2+1)) ((n^2 : ℕ) : ℤ))
  rw [word_exact (k:=2) hn le_rfl] at h
  apply lt_of_lt_of_le (by simpa using h : (n:ℤ)^2 < (2:ℤ)^((2+2)*(n.log2+1)-1))
  exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hb) 1)

private theorem fits_range {W n : ℕ} {z : ℤ} (capacity : Capacity W n)
    (lo : -((n:ℤ)^2) ≤ z) (hi : z ≤ (n:ℤ)^2) : Fits W z :=
  ⟨(neg_le_neg (le_of_lt capacity)).trans lo, hi.trans_lt capacity⟩

theorem fits_address {W n : ℕ} (cap : Capacity W n) (u v : Fin n) :
    Fits W (address u v) := by
  have hv := v.isLt
  have hh := Nat.mul_le_mul_right n u.isLt
  have hh' : 1+u.val*n+v.val ≤ n*n := by rw [Nat.succ_mul] at hh; omega
  apply fits_range cap
  · exact le_trans (neg_nonpos.mpr (sq_nonneg _)) (Int.natCast_nonneg _)
  · dsimp [address]
    rw [sq]
    exact_mod_cast hh'

theorem fits_difference {W n : ℕ} (cap : Capacity W n) (u v : Fin n) :
    Fits W ((u.val:ℤ)-v.val) := by
  have hu : (u.val:ℤ)<n := by exact_mod_cast u.isLt
  have hv : (v.val:ℤ)<n := by exact_mod_cast v.isLt
  have hsq : (n:ℤ) ≤ (n:ℤ)^2 := by nlinarith [Int.natCast_nonneg u.val]
  apply fits_range cap <;> omega

theorem fits_before_zero {W n : ℕ} (cap : Capacity W n) (u : Fin n) :
    Fits W ((u.val:ℤ)-1) := by
  have hu : (u.val:ℤ)<n := by exact_mod_cast u.isLt
  have hsq : (n:ℤ) ≤ (n:ℤ)^2 := by nlinarith [Int.natCast_nonneg u.val]
  apply fits_range cap <;> omega

namespace Reg
abbrev acc : ℤ := -1
abbrev test : ℤ := -2
abbrev ptr : ℤ := -3
abbrev value : ℤ := -4
abbrev one : ℤ := -5
end Reg

/-- Embedded row-major probe. The caller keeps the constant one in cell -5.
There is no accepting instruction between probes. -/
def probe (x y : ℤ) : Command :=
  .seq (.atom (.mul Reg.ptr 0 x))
  (.seq (.atom (.add Reg.ptr Reg.ptr y))
  (.seq (.atom (.add Reg.ptr Reg.ptr Reg.one))
        (.atom (.load Reg.value Reg.ptr))))

def probed (m : Memory) (a z : ℤ) := update (update m Reg.ptr a) Reg.value z

private theorem overwrite (m : Memory) (d x y : ℤ) :
    update (update m d x) d y = update m d y := by
  funext a
  by_cases e : a = d <;> simp [update,e]

theorem probe_runs {W n : ℕ} {G : SimpleGraph (Fin n)} {m : Memory} (u v : Fin n)
    {x y : ℤ} (_hx : x ≤ -6) (hy : y ≤ -6) (hu : m x = u.val) (hv : m y = v.val)
    (one : m Reg.one = 1) (gr : GraphAt G m) (cap : Capacity W n) :
    Runs W (probe x y) m 4 (probed m (address u v) (if G.Adj u v then 1 else 0)) := by
  let m₁ := update m Reg.ptr (m 0*m x)
  let m₂ := update m₁ Reg.ptr (m₁ Reg.ptr+m₁ y)
  let m₃ := update m₂ Reg.ptr (m₂ Reg.ptr+m₂ Reg.one)
  have hp : m₃ Reg.ptr = address u v := by
    have hy' : y ≠ Reg.ptr := by change y ≠ -3; omega
    simp [m₃,m₂,m₁,update,hy',Reg.ptr,Reg.one,hu,hv,gr.1,one,address] at *
    ring
  have hptr : m₃ = update m Reg.ptr (address u v) := by
    unfold m₃ m₂ m₁
    rw [overwrite,overwrite]
    exact congrArg _ hp
  have ha : address u v ≠ Reg.ptr := by
    have hh : 0 ≤ address u v := Int.natCast_nonneg _
    change address u v ≠ -3
    omega
  have hz : m₃ (m₃ Reg.ptr) = if G.Adj u v then 1 else 0 := by
    rw [hp,hptr]
    simpa [update,ha] using gr.2 u v
  have hf : Fits W (m₃ Reg.ptr) := hp.symm ▸ fits_address cap u v
  have run : Runs W (probe x y) m 4 (update m₃ Reg.value (m₃ (m₃ Reg.ptr))) :=
    Runs.seq (t:=3) (.atom (.mul _ _ _ _))
      (.seq (t:=2) (.atom (.add _ _ _ _))
        (.seq (.atom (.add _ _ _ _)) (.atom (.load _ _ _ hf))))
  rwa [hz,hptr] at run

theorem probe_frame (m : Memory) (a z : ℤ) : Frame m (probed m a z) :=
  (Frame.write _ (by decide : -5 < Reg.ptr ∧ Reg.ptr < 0) _).trans
    (Frame.write _ (by decide : -5 < Reg.value ∧ Reg.value < 0) _)

end VWZClique.IntegerRAM.Graph
end

/- WordGraphDivide -/
section
/-! Repeated subtraction for radix decoding. It uses one graph-order cell and
four negative cells, with a time linear in the quotient. A blocked input table
can afford linear work per packed key. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Division

def state (m : Memory) (z q s : ℤ) : Memory :=
  update (update (update m num z) quot q) test s

theorem state_frame (m : Memory) (z q s : ℤ) : Frame m (state m z q s) :=
  ((Frame.write _ (by decide : -5 < num ∧ num < 0) _).trans
    (Frame.write _ (by decide : -5 < quot ∧ quot < 0) _)).trans
    (Frame.write _ (by decide : -5 < test ∧ test < 0) _)

theorem state_num (m : Memory) (z q s : ℤ) : state m z q s num = z := by
  simp [state,update,num,quot,test]

theorem state_quot (m : Memory) (z q s : ℤ) : state m z q s quot = q := by
  simp [state,update,quot,test]

theorem state_test (m : Memory) (z q s : ℤ) : state m z q s test = s := by
  simp [state,update]

theorem body_runs {W : ℕ} (m : Memory) (ho : m one=1) :
    Runs W body m 4 (state m (m num-m 0) (m quot+1) (m 0-(m num-m 0)-1)) := by
  let m₁ := update m num (m num-m 0)
  let m₂ := update m₁ quot (m₁ quot + m₁ one)
  let m₃ := update m₂ test (m₂ 0-m₂ num)
  let m₄ := update m₃ test (m₃ test-m₃ one)
  have run : Runs W body m 4 m₄ :=
    Runs.seq (t:=3) (.atom (.sub _ _ _ _))
      (.seq (t:=2) (.atom (.add _ _ _ _)) (.seq (.atom (.sub _ _ _ _)) (.atom (.sub _ _ _ _))))
  convert run using 1
  funext p
  by_cases h : p=test <;> simp [h,m₄,m₃,m₂,m₁,state,update,num,quot,test,one] at *
  all_goals simp [←ho]

theorem room_pow {b n k : ℕ} (hn : 1 ≤ n) (hb : k+2 ≤ b) :
    Room (b*(n.log2+1)) (n^k) := by
  have h := BitVec.toInt_lt (x := BitVec.ofInt ((k+2)*(n.log2+1)) ((n^k:ℕ):ℤ))
  rw [word_exact (k:=k) hn le_rfl] at h
  exact h.trans_le (pow_le_pow_right₀ (by norm_num)
    (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hb) 1))

/-- Execute exactly q positive subtraction rounds, starting with q*n+r.
The quotient register can already contain an arbitrary accumulator. -/
theorem loop_runs {W M n r : ℕ} (cap : Room W M) (hnM : n ≤ M) (hr : r<n)
    (q : ℕ) (hq : 0<q) (ha : q*n+r ≤ M) (m : Memory)
    (dn : m 0 = n) (ho : m one=1) (hn : m num = ((q*n+r:ℕ):ℤ)) :
    ∃ out, Runs W loop m (5*q) out ∧ Frame m out ∧ out num = r ∧ out quot = m quot+q := by
  induction q generalizing m with
  | zero => omega
  | succ q ih =>
    let v : ℤ := ((q*n+r:ℕ):ℤ)
    let d : ℤ := (n:ℤ)-v-1
    let y := state m v (m quot+1) d
    have subn : m num-m 0=v := by rw [hn,dn]; dsimp [v]; ring
    have act : Runs W body m 4 y := by
      have h := body_runs (W:=W) m ho
      rw [subn,dn] at h
      exact h
    have fy : Frame m y := state_frame m v (m quot+1) d
    have ynum : y num = v := state_num .. 
    have yquot : y quot = m quot+1 := state_quot .. 
    have ytest : y test = d := state_test ..
    have hvn : q*n+r ≤ M := by rw [Nat.succ_mul] at ha; omega
    have hv : v ≤ (M:ℤ) := by dsimp [v]; exact_mod_cast hvn
    have hnv : 0 ≤ v := Int.natCast_nonneg _
    have hN : (n:ℤ) ≤ M := by exact_mod_cast hnM
    have hNpos : 0 < (n:ℤ) := by exact_mod_cast (show 0<n by omega)
    have hf : Fits W (y test) := by rw [ytest]; apply cap.fits <;> dsimp [d] <;> omega
    by_cases done : q = 0
    · subst q
      have hvr : v=(r:ℤ) := by simp [v]
      refine ⟨y,?_,fy,ynum.trans hvr,by simpa using yquot⟩
      have nonneg : ¬ y test<0 := by rw [ytest]; dsimp [d]; rw [hvr]; omega
      exact Runs.loop_done act hf nonneg
    · have hqn : 1 ≤ q := by omega
      have hnb : n ≤ q*n+r := by
        have := Nat.mul_le_mul_right n hqn
        omega
      have hn' : (n:ℤ) ≤ v := by dsimp [v]; exact_mod_cast hnb
      have neg : y test<0 := by rw [ytest]; dsimp [d]; omega
      obtain ⟨out,more,fr,rem,result⟩ := ih (by omega) hvn y
        ((fy _ (Or.inr le_rfl)).trans dn) ((fy _ (Or.inl (by decide : one≤ -5))).trans ho) ynum
      refine ⟨out,?_,fy.trans fr,rem,?_⟩
      · rw [show 5*(q+1)=4+1+5*q by omega]
        exact Runs.loop_again act hf neg more
      · rw [result,yquot]
        push_cast
        ring

/-- Native Euclidean quotient and remainder. It takes three setup/guard
instructions and precisely five instructions per quotient unit. -/
theorem command_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (ha : m num=a) :
    ∃ out, Runs W command m (3+5*(a/n)) out ∧ Frame m out ∧
      out num = ((a%n:ℕ):ℤ) ∧ out quot = ((a/n:ℕ):ℤ) := by
  let x := update m quot 0
  let y := update x test ((a:ℤ)-n)
  have fx : Frame m x := Frame.write _ (by decide : -5 < quot ∧ quot < 0) _
  have fy : Frame m y := fx.trans (Frame.write _ (by decide : -5 < test ∧ test < 0) _)
  have act₁ : Runs W (.atom (.sub quot quot quot)) m 1 x := by
    simpa [x] using Runs.atom (Step.sub (W:=W) m quot quot quot)
  have xn : x num=(a:ℤ) := by simpa [x,update,num,quot] using ha
  have xd : x 0=(n:ℤ) := (fx _ (Or.inr le_rfl)).trans dn
  have act₂ : Runs W (.atom (.sub test num 0)) x 1 y := by
    simpa only [y,xn,xd] using Runs.atom (Step.sub (W:=W) x test num 0)
  have yt : y test=(a:ℤ)-n := by simp [y,update]
  have yq : y quot=0 := by simp [y,x,update,quot,test]
  have yn : y num=(a:ℤ) := by simpa [y,x,update,num,quot,test] using ha
  have hf : Fits W (y test) := by rw [yt]; apply cap.fits <;> omega
  by_cases small : a<n
  · have q0 := Nat.div_eq_of_lt small
    have r0 := Nat.mod_eq_of_lt small
    have neg : y test<0 := by omega
    refine ⟨y,?_,fy,by simpa only [r0] using yn,by simpa only [q0,Nat.cast_zero] using yq⟩
    simpa [command,q0] using Runs.seq act₁ (.seq act₂ (Runs.guard_skip (c:=loop) hf neg))
  · have ge : n≤a := by omega
    have qpos : 0<a/n := Nat.div_pos ge hn
    have parts : a/n*n+a%n=a := by rw [Nat.add_comm,Nat.mul_comm, Nat.mod_add_div]
    have nonneg : ¬ y test<0 := by omega
    obtain ⟨out,more,fr,rem,qout⟩ := loop_runs cap hnM (Nat.mod_lt a hn) (a/n) qpos
      (by simpa only [parts] using haM) y ((fy _ (Or.inr le_rfl)).trans dn)
      ((fy _ (Or.inl (by decide : one≤ -5))).trans ho) (by simpa only [parts] using yn)
    refine ⟨out,?_,fy.trans fr,rem,by simpa [yq] using qout⟩
    simpa only [command,show 1+(1+(1+5*(a/n)))=3+5*(a/n) by omega] using
      Runs.seq act₁ (.seq act₂ (Runs.guard_take hf nonneg more))

end Division
end VWZClique.IntegerRAM.Graph
end

/- WordGraphTests -/
section
namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical

/-- Inputs to a weight test are held in a fixed collection of vertex registers. -/
inductive Test (ι : Type*) where
  | zero (u : ι)
  | edge (u v : ι)

def Test.holds {ι : Type*} {n : ℕ} (G : SimpleGraph (Fin n)) (d : ι → Fin n) :
    Test ι → Prop
  | .zero u => (d u).val = 0
  | .edge u v => d u < d v ∧ G.Adj (d u) (d v)

def mask (t r : ℤ) : Command := .whenNonnegative t (.atom (.sub r r r))

def masked (m : Memory) (t r : ℤ) : Memory :=
  if m t < 0 then m else update m r 0

theorem mask_runs {W : ℕ} (m : Memory) (t r : ℤ) (hf : Fits W (m t)) :
    Runs W (mask t r) m (if m t < 0 then 1 else 2) (masked m t r) := by
  by_cases h : m t < 0
  · simpa [mask,masked,h] using Runs.guard_skip (c:=.atom (.sub r r r)) hf h
  · have z : Runs W (.atom (.sub r r r)) m 1 (update m r 0) := by
      simpa using Runs.atom (Step.sub (W:=W) m r r r)
    simpa [mask,masked,h] using Runs.guard_take hf h z

theorem mask_frame (m : Memory) (t r : ℤ) (hr : -5 < r ∧ r < 0) :
    Frame m (masked m t r) := by
  by_cases h : m t < 0
  · simpa [masked,h] using Frame.refl m
  · simpa [masked,h] using Frame.write m hr 0

def Test.code {ι : Type*} (a : ι → ℤ) : Test ι → Command
  | .zero u => .seq (.atom (.sub Reg.test (a u) Reg.one)) (mask Reg.test Reg.acc)
  | .edge u v => .seq (probe (a u) (a v))
      (.seq (.atom (.sub Reg.test (a u) (a v)))
      (.seq (mask Reg.test Reg.value) (.atom (.mul Reg.acc Reg.acc Reg.value))))

/-- Branch costs are exact, including a taken guard and its single subtraction. -/
def Test.ticks {ι : Type*} {n : ℕ} (d : ι → Fin n) : Test ι → ℕ
  | .zero u => 1 + (if (d u).val = 0 then 1 else 2)
  | .edge u v => 4 + (1 + ((if d u < d v then 1 else 2) + 1))

theorem Test.ticks_le {ι : Type*} {n : ℕ} (d : ι → Fin n) (c : Test ι) :
    c.ticks d ≤ 8 := by
  cases c <;> simp only [ticks] <;> split <;> decide

theorem test_runs {ι : Type*} {W n : ℕ} {G : SimpleGraph (Fin n)}
    (a : ι → ℤ) (ha : ∀ i, a i ≤ -6) (d : ι → Fin n) {m : Memory}
    (hm : ∀ i, m (a i) = (d i).val) (one : m Reg.one = 1) (gr : GraphAt G m)
    (cap : Capacity W n) (c : Test ι) :
    ∃ out, Runs W (c.code a) m (c.ticks d) out ∧ Frame m out ∧
      out Reg.acc = if c.holds G d then m Reg.acc else 0 := by
  classical
  cases c with
  | zero u =>
    let m₁ := update m Reg.test (((d u).val:ℤ)-1)
    have act : Runs W (.atom (.sub Reg.test (a u) Reg.one)) m 1 m₁ := by
      simpa only [m₁,hm,one] using Runs.atom (Step.sub (W:=W) m Reg.test (a u) Reg.one)
    have value : m₁ Reg.test = ((d u).val:ℤ)-1 := by simp [m₁,update]
    have cmp : m₁ Reg.test<0 ↔ (d u).val=0 := by rw [value]; omega
    have hf : Fits W (m₁ Reg.test) := value.symm ▸ fits_before_zero cap (d u)
    let out := masked m₁ Reg.test Reg.acc
    have fr := (Frame.write m (by decide : -5 < Reg.test ∧ Reg.test < 0) _).trans
      (mask_frame m₁ Reg.test Reg.acc (by decide))
    refine ⟨out,?_,fr,?_⟩
    · simpa only [Test.code,Test.ticks,cmp] using Runs.seq act (mask_runs m₁ Reg.test Reg.acc hf)
    · by_cases h : (d u).val=0
      · simp [Test.holds,h,out,masked,m₁,update,Reg.acc,Reg.test]
      · simp [Test.holds,h,out,masked,cmp,update]
  | edge u v =>
    let bit : ℤ := if G.Adj (d u) (d v) then 1 else 0
    let m₁ := probed m (address (d u) (d v)) bit
    let m₂ := update m₁ Reg.test (((d u).val:ℤ)-(d v).val)
    let m₃ := masked m₂ Reg.test Reg.value
    let out := update m₃ Reg.acc (m₃ Reg.acc * m₃ Reg.value)
    have act₁ : Runs W (probe (a u) (a v)) m 4 m₁ :=
      probe_runs _ _ (ha u) (ha v) (hm u) (hm v) one gr cap
    have fr₁ : Frame m m₁ := probe_frame m _ bit
    have regs (i : _) : m₁ (a i) = (d i).val :=
      (fr₁ _ (Or.inl (by have := ha i; omega))).trans (hm i)
    have act₂ : Runs W (.atom (.sub Reg.test (a u) (a v))) m₁ 1 m₂ := by
      simpa only [m₂,regs] using Runs.atom (Step.sub (W:=W) m₁ Reg.test (a u) (a v))
    have value : m₂ Reg.test = ((d u).val:ℤ)-(d v).val := by simp [m₂,update]
    have cmp : m₂ Reg.test < 0 ↔ d u < d v := by
      rw [value,sub_neg]
      exact_mod_cast (Iff.rfl : (d u).val < (d v).val ↔ d u < d v)
    have hf : Fits W (m₂ Reg.test) := value.symm ▸ fits_difference cap (d u) (d v)
    have act₃ := mask_runs m₂ Reg.test Reg.value hf
    have act₄ : Runs W (.atom (.mul Reg.acc Reg.acc Reg.value)) m₃ 1 out :=
      .atom (.mul ..)
    have fr₂ : Frame m₁ m₂ := Frame.write _ (by decide : -5 < Reg.test ∧ Reg.test < 0) _
    have fr₃ : Frame m₂ m₃ := mask_frame _ _ _ (by decide)
    have fr₄ : Frame m₃ out := Frame.write _ (by decide : -5 < Reg.acc ∧ Reg.acc < 0) _
    have data : m₂ Reg.value = bit := by simp [m₂,m₁,probed,update,Reg.value,Reg.test]
    have acc : m₂ Reg.acc = m Reg.acc := by simp [m₂,m₁,probed,update,Reg.acc,Reg.ptr,Reg.value,Reg.test]
    refine ⟨out,?_,((fr₁.trans fr₂).trans fr₃).trans fr₄,?_⟩
    · simpa only [Test.code,Test.ticks,cmp] using Runs.seq act₁ (.seq act₂ (.seq act₃ act₄))
    · by_cases h : d u < d v
      · by_cases adj : G.Adj (d u) (d v) <;>
          simp [Test.holds,h,adj,out,m₃,masked,cmp.mpr h,update,data,acc,bit]
      · have nneg : ¬ m₂ Reg.test < 0 := fun p => h (cmp.mp p)
        simp [Test.holds,h,out,m₃,masked,nneg,update]

def commands {ι : Type*} (a : ι → ℤ) : List (Test ι) → Command
  | [] => .skip
  | c::cs => .seq (c.code a) (commands a cs)

theorem commands_runs {ι : Type*} {W n : ℕ} {G : SimpleGraph (Fin n)}
    (a : ι → ℤ) (ha : ∀ i, a i ≤ -6) (d : ι → Fin n) (cs : List (Test ι))
    (cap : Capacity W n) {m : Memory} (hm : ∀ i, m (a i) = (d i).val)
    (one : m Reg.one = 1) (gr : GraphAt G m) :
    ∃ out, Runs W (commands a cs) m (cs.map (Test.ticks d)).sum out ∧ Frame m out ∧
      out Reg.acc = if ∀ c ∈ cs, c.holds G d then m Reg.acc else 0 := by
  classical
  induction cs generalizing m with
  | nil => exact ⟨m,.skip _,Frame.refl _,by simp⟩
  | cons c cs ih =>
    obtain ⟨m₁,act,fr,acc⟩ := test_runs a ha d hm one gr cap c
    obtain ⟨out,more,fr',final⟩ := ih (m:=m₁)
      (fun i => (fr _ (Or.inl (by have := ha i; omega))).trans (hm i))
      ((fr _ (Or.inl (by decide : Reg.one ≤ -5))).trans one) (gr.frame fr)
    refine ⟨out,.seq act more,fr.trans fr',?_⟩
    rw [final,acc]
    by_cases h : c.holds G d <;> by_cases hs : ∀ j ∈ cs, j.holds G d <;> simp [h,hs]

theorem commands_ticks_le {ι : Type*} {n : ℕ} (d : ι → Fin n) (cs : List (Test ι)) :
    (cs.map (Test.ticks d)).sum ≤ cs.length * 8 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    have := c.ticks_le d
    omega

end VWZClique.IntegerRAM.Graph
end

/- WordGraphWeights -/
section
/-! Fixed native code for every blocked unary or edge weight. The two block
labels are supplied as vertex digits in read-only registers. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction Classical
open TrulySubcubicAPSP

private def foreach {ι : Type*} {t : ℕ} (f : Fin t → List ι) : List ι :=
  (List.finRange t).flatMap f

private theorem foreach_iff {ι : Type*} {t : ℕ} (f : Fin t → List ι) (P : ι → Prop) :
    (∀ c ∈ foreach f, P c) ↔ ∀ i, ∀ c ∈ f i, P c := by
  constructor
  · intro h i c hc
    exact h c (List.mem_flatMap.mpr ⟨i,by simp,hc⟩)
  · intro h c hc
    obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
    exact h i c hc

private theorem foreach_length {ι : Type*} {t B : ℕ} (f : Fin t → List ι)
    (h : ∀ i, (f i).length ≤ B) : (foreach f).length ≤ t*B := by
  have go (xs : List (Fin t)) : (xs.flatMap f).length ≤ xs.length * B := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
      have hb := h i
      omega
  simpa [foreach] using go (List.finRange t)

/-- The two operands of an ordered-edge test depend only on the fixed slot
positions and on which positions precede the clique-size cutoff. -/
def pairTests {ι : Type*} {t : ℕ} (k : ℕ) (r s : Fin (9*t)) (x y : ι) : List (Test ι) :=
  if r.val < k ∧ s.val < k then
    if r < s then [.edge x y] else if s < r then [.edge y x] else []
  else []

theorem pairTests_iff {ι : Type*} {t n : ℕ} (G : SimpleGraph (Fin n)) (d : ι → Fin n)
    (k : ℕ) (r s : Fin (9*t)) (x y : ι) :
    (∀ c ∈ pairTests k r s x y, c.holds G d) ↔ compatible G k r s (d x) (d y) := by
  by_cases hr : r.val < k
  · by_cases hs : s.val < k
    · rcases lt_trichotomy r s with h|rfl|h
      · simp [pairTests,compatible,Test.holds,hr,hs,h,h.asymm]
      · simp [pairTests,compatible,hr]
      · simp [pairTests,compatible,Test.holds,hr,hs,h,h.asymm]
    · simp [pairTests,compatible,hs]
  · simp [pairTests,compatible,hr]

theorem pairTests_length {ι : Type*} {t : ℕ} (k : ℕ) (r s : Fin (9*t)) (x y : ι) :
    (pairTests k r s x y).length ≤ 1 := by
  unfold pairTests
  split_ifs <;> simp

def crossTests {ι : Type*} {t : ℕ} (k : ℕ) (i j : V) (x y : Fin t → ι) : List (Test ι) :=
  foreach fun p => foreach fun q => pairTests k (slot i p) (slot j q) (x p) (y q)

theorem crossTests_iff {ι : Type*} {n t : ℕ} (G : SimpleGraph (Fin n)) (d : ι → Fin n)
    (k : ℕ) (i j : V) (x y : Fin t → ι) :
    (∀ c ∈ crossTests k i j x y, c.holds G d) ↔
      ∀ p q, compatible G k (slot i p) (slot j q) (d (x p)) (d (y q)) := by
  simp only [crossTests,foreach_iff,pairTests_iff]

theorem crossTests_length {ι : Type*} {t : ℕ} (k : ℕ) (i j : V) (x y : Fin t → ι) :
    (crossTests k i j x y).length ≤ t*t := by
  apply foreach_length
  intro p
  simpa using foreach_length _ (fun q => pairTests_length k (slot i p) (slot j q) (x p) (y q))

abbrev Side (t : ℕ) := Fin t ⊕ Fin t

def padTests {t : ℕ} (k : ℕ) (i : V) : List (Test (Side t)) :=
  foreach fun p => if k ≤ (slot i p).val then [.zero (.inl p)] else []

theorem padTests_iff {n t : ℕ} (G : SimpleGraph (Fin n)) (d : Side t → Fin n)
    (k : ℕ) (i : V) :
    (∀ c ∈ padTests k i, c.holds G d) ↔ ∀ p, k ≤ (slot i p).val → (d (.inl p)).val = 0 := by
  rw [padTests,foreach_iff]
  apply forall_congr'
  intro p
  by_cases h : k ≤ (slot i p).val <;> simp [h,Test.holds]

theorem padTests_length {t : ℕ} (k : ℕ) (i : V) : (padTests (t:=t) k i).length ≤ t := by
  unfold padTests
  suffices H : (foreach (fun p : Fin t => if k ≤ (slot i p).val then
      [Test.zero (Sum.inl p : Side t)] else [])).length ≤ t*1 by simpa using H
  apply foreach_length
  intro p
  split <;> simp

/-- One unary group or an ordered pair of groups. Its program is independent of n
and of the graph. -/
inductive Shape where
  | unary (i : V)
  | cross (i j : V)

def Shape.tests {t : ℕ} (k : ℕ) : Shape → List (Test (Side t))
  | .unary i => padTests k i ++ crossTests k i i Sum.inl Sum.inl
  | .cross i j => crossTests k i j Sum.inl Sum.inr

def Shape.key {n t : ℕ} (x y : Fin (n^t)) : Shape → WeightKey (n^t)
  | .unary i => .inl (i,x)
  | .cross i j => .inr (i,j,x,y)

def digits {n t : ℕ} (x y : Fin (n^t)) : Side t → Fin n := Sum.elim (digit x) (digit y)

theorem shape_value {n t : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (x y : Fin (n^t))
    (k : ℕ) (s : Shape) :
    (if ∀ c ∈ s.tests (t:=t) k, c.holds G (digits x y) then (1:ℚ) else 0) =
      weights G k ⟨0,hn⟩ (s.key x y) := by
  cases s with
  | unary i =>
    have h : (∀ c ∈ (Shape.unary i).tests (t:=t) k, c.holds G (digits x y)) ↔
        unaryOK G k ⟨0,hn⟩ i x := by
      simp only [Shape.tests,List.forall_mem_append,padTests_iff,crossTests_iff,unaryOK,
        digits,Sum.elim_inl,Fin.ext_iff]
    simp only [h,Shape.key,weights]
  | cross i j =>
    have h : (∀ c ∈ (Shape.cross i j).tests (t:=t) k, c.holds G (digits x y)) ↔
        edgeOK G k i j x y := by
      simp only [Shape.tests,crossTests_iff,edgeOK,digits,Sum.elim_inl,Sum.elim_inr]
    simp only [h,Shape.key,weights]

theorem shape_length {t : ℕ} (k : ℕ) (s : Shape) : (s.tests (t:=t) k).length ≤ t+t*t := by
  cases s with
  | unary i => exact List.length_append ▸ Nat.add_le_add (padTests_length k i) (crossTests_length ..)
  | cross i j => exact (crossTests_length k i j _ _).trans (Nat.le_add_left _ _)

def digitRegister {t : ℕ} : Side t → ℤ
  | .inl p => -6 - 2*(p.val:ℤ)
  | .inr p => -7 - 2*(p.val:ℤ)

theorem digitRegister_le {t : ℕ} (i : Side t) : digitRegister i ≤ -6 := by
  cases i <;> simp only [digitRegister] <;> omega

def Shape.command {t : ℕ} (k : ℕ) (s : Shape) : Command :=
  .seq (.atom (.one Reg.one)) (.seq (.atom (.one Reg.acc)) (commands digitRegister (s.tests (t:=t) k)))

def Shape.cost {n t : ℕ} (k : ℕ) (s : Shape) (x y : Fin (n^t)) : ℕ :=
  1+(1+((s.tests k).map (Test.ticks (digits x y))).sum)

theorem cost_le {n t : ℕ} (k : ℕ) (s : Shape) (x y : Fin (n^t)) :
    s.cost k x y ≤ 2 + (t+t*t)*8 := by
  have h := commands_ticks_le (digits x y) (s.tests k)
  have hlen := shape_length (t:=t) k s
  unfold Shape.cost
  omega

/-- Compute a blocked weight from the original graph cells and the two arrays of
vertex digits. All nonnegative memory and all digit registers are preserved. -/
theorem weight_runs {W n t : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (k : ℕ)
    (s : Shape) (x y : Fin (n^t)) {m : Memory} (gr : GraphAt G m) (cap : Capacity W n)
    (reg : ∀ i : Side t, m (digitRegister i) = (digits x y i).val) :
    ∃ out, Runs W (s.command (t:=t) k) m (s.cost k x y) out ∧
      (out Reg.acc : ℚ) = weights G k ⟨0,hn⟩ (s.key x y) ∧
      ∀ z : ℤ, z ≤ -6 ∨ 0 ≤ z → out z = m z := by
  let m₁ := update m Reg.one 1
  let m₂ := update m₁ Reg.acc 1
  have keep (z : ℤ) (hz : z ≤ -6 ∨ 0 ≤ z) : m₂ z = m z := by
    have h1 : z ≠ Reg.one := by rcases hz with h|h <;> change z ≠ -5 <;> omega
    have h2 : z ≠ Reg.acc := by rcases hz with h|h <;> change z ≠ -1 <;> omega
    simp [m₂,m₁,update,h1,h2]
  have graph : GraphAt G m₂ := ⟨(keep 0 (Or.inr le_rfl)).trans gr.1,fun u v =>
    (keep _ (Or.inr (Int.natCast_nonneg _))).trans (gr.2 u v)⟩
  have one : m₂ Reg.one=1 := by simp [m₂,m₁,update,Reg.one,Reg.acc]
  have acc : m₂ Reg.acc=1 := by simp [m₂,update]
  obtain ⟨out,run,fr,ans⟩ := commands_runs digitRegister digitRegister_le (digits x y) (s.tests k) cap
    (fun i => (keep _ (Or.inl (digitRegister_le i))).trans (reg i)) one graph
  refine ⟨out,.seq (.atom (.one ..)) (.seq (.atom (.one ..)) run),?_,?_⟩
  · rw [ans,acc,←shape_value hn G x y k s]
    split_ifs <;> norm_num
  · intro z hz
    exact (fr z (hz.imp (fun h => by omega) id)).trans (keep z hz)

end VWZClique.IntegerRAM.Graph
end

/- WordGraphDigits -/
section
/-! Radix-n unpacking of a blocked vertex label by the native word machine. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Digits
open Division

theorem step_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (ha : m num=a) (r : ℤ) (hr : r ≤ -6) :
    ∃ out, Runs W (step r) m (5+5*(a/n)) out ∧ out num = ((a/n:ℕ):ℤ) ∧
      out r = ((a%n:ℕ):ℤ) ∧ ∀ z, Protected z → z ≠ r → out z=m z := by
  obtain ⟨v,division,fr,rem,q⟩ := command_runs hn cap hnM haM m dn ho ha
  let x := update v r ((a%n:ℕ):ℤ)
  let y := update x num ((a/n:ℕ):ℤ)
  have vone : v one=1 := (fr _ (Or.inl (by decide : one ≤ -5))).trans ho
  have rr : r ≠ num := by change r ≠ -1; omega
  have hq : quot ≠ r := by change -2 ≠ r; omega
  have h1 : one ≠ r := by change -5 ≠ r; omega
  have first : Runs W (.atom (.mul r num one)) v 1 x := by
    simpa only [rem,vone,mul_one,x] using Runs.atom (Step.mul (W:=W) v r num one)
  have xq : x quot=((a/n:ℕ):ℤ) := by simpa [x,update,hq] using q
  have xone : x one=1 := by simpa [x,update,h1] using vone
  have second : Runs W (.atom (.mul num quot one)) x 1 y := by
    simpa only [xq,xone,mul_one,y] using Runs.atom (Step.mul (W:=W) x num quot one)
  refine ⟨y,?_,by simp [y,update],by simp [y,x,update,rr],?_⟩
  · simpa only [step,show 3+5*(a/n)+(1+1) = 5+5*(a/n) by omega] using
      Runs.seq division (Runs.seq first second)
  · intro z hz hz'
    have hznum : z ≠ num := by rcases hz with h|h <;> change z ≠ -1 <;> omega
    simpa [y,x,update,hznum,hz'] using fr z hz

/-- The fixed code emits one digit register per slot, least significant first. -/
def loop (atCell : ℕ → ℤ) : ℕ → Command
  | 0 => .skip
  | j+1 => .seq (loop atCell j) (step (atCell j))

def cost (n a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => cost n a j + (5+5*(a/n^j/n))

theorem cost_le (n a L : ℕ) : cost n a L ≤ L*(5+5*a) := by
  induction L with
  | zero => simp [cost]
  | succ L ih =>
    change cost n a L + (5+5*(a/n^L/n)) ≤ (L+1)*(5+5*a)
    rw [Nat.add_mul,one_mul]
    have h : a/n^L/n ≤ a := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    omega

theorem loop_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (ha : m num=a)
    (atCell : ℕ → ℤ) (reg : ∀ p, atCell p ≤ -6) (inj : Function.Injective atCell) (L : ℕ) :
    ∃ out, Runs W (loop atCell L) m (cost n a L) out ∧
      out num = ((a/n^L:ℕ):ℤ) ∧ (∀ p<L, out (atCell p) = ((a/n^p%n:ℕ):ℤ)) ∧
      ∀ z, Protected z → (∀ p<L, z ≠ atCell p) → out z=m z := by
  induction L with
  | zero => exact ⟨m,.skip _,by simpa using ha,by omega,fun _ _ _ => rfl⟩
  | succ L ih =>
    obtain ⟨x,act,hnum,hd,hf⟩ := ih
    have x0 : x 0=n := (hf _ (Or.inr le_rfl) (fun p _ => by have := reg p; omega)).trans dn
    have xo : x one=1 := (hf _ (Or.inl (by decide : one≤ -5)) (fun p _ => by
      have := reg p; change -5 ≠ atCell p; omega)).trans ho
    obtain ⟨out,more,oq,orr,keep⟩ := step_runs hn cap hnM ((Nat.div_le_self _ _).trans haM)
      x x0 xo hnum (atCell L) (reg L)
    refine ⟨out,.seq act more,?_,?_,?_⟩
    · simpa only [pow_succ,Nat.div_div_eq_div_mul] using oq
    · intro p hp
      by_cases h : p=L
      · subst p; exact orr
      · exact (keep _ (Or.inl (by have := reg p; omega)) (fun he => h (inj he))).trans
          (hd p (by omega))
    · intro z hz hh
      exact (keep z hz (hh L (by omega))).trans (hf z hz (fun p hp => hh p (by omega)))

def unpack (src : ℤ) (atCell : ℕ → ℤ) (L : ℕ) : Command :=
  .seq (.atom (.mul num src one)) (loop atCell L)

theorem unpack_runs {W M n a : ℕ} (hn : 0<n) (cap : Room W M) (hnM : n≤M) (haM : a≤M)
    (m : Memory) (dn : m 0=n) (ho : m one=1) (src : ℤ) (ha : m src=a)
    (atCell : ℕ → ℤ) (reg : ∀ p, atCell p ≤ -6) (inj : Function.Injective atCell) (L : ℕ) :
    ∃ out, Runs W (unpack src atCell L) m (1+cost n a L) out ∧
      (∀ p<L, out (atCell p) = ((a/n^p%n:ℕ):ℤ)) ∧
      ∀ z, Protected z → (∀ p<L, z ≠ atCell p) → out z=m z := by
  let x := update m num a
  have act : Runs W (.atom (.mul num src one)) m 1 x := by
    simpa only [x,ha,ho,mul_one] using Runs.atom (Step.mul (W:=W) m num src one)
  have frame : Frame m x := Frame.write _ (by decide : -5<num ∧ num<0) _
  have hx : x num=(a:ℤ) := by simp [x,update]
  obtain ⟨out,more,_,d,keep⟩ := loop_runs hn cap hnM haM x ((frame _ (Or.inr le_rfl)).trans dn)
    ((frame _ (Or.inl (by decide : one≤ -5))).trans ho) hx atCell reg inj L
  exact ⟨out,.seq act more,d,fun z hz hp => (keep z hz hp).trans (frame _ hz)⟩

end Digits
end VWZClique.IntegerRAM.Graph
end

/- WordGraphPacked -/
section
/-! Fixed native computation of one grouped graph weight from two packed integer
labels and the original row-major adjacency array. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction
open TrulySubcubicAPSP

def leftCell (p : ℕ) : ℤ := -6-2*(p:ℤ)
def rightCell (p : ℕ) : ℤ := -7-2*(p:ℤ)
def leftArg (t : ℕ) : ℤ := -8-2*(t:ℤ)
def rightArg (t : ℕ) : ℤ := -9-2*(t:ℤ)

def Kept (t : ℕ) (z : ℤ) : Prop :=
  (z ≤ -6 ∨ 0 ≤ z) ∧ ∀ p<t, z ≠ leftCell p ∧ z ≠ rightCell p

theorem kept_nonneg {z : ℤ} (hz : 0 ≤ z) (t : ℕ) : Kept t z := by
  refine ⟨Or.inr hz,?_⟩
  intro p _
  simp only [leftCell,rightCell]
  omega

theorem kept_leftArg (t : ℕ) : Kept t (leftArg t) := by
  constructor
  · left; unfold leftArg; omega
  · intro p h; simp only [leftArg,leftCell,rightCell]; omega

theorem kept_rightArg (t : ℕ) : Kept t (rightArg t) := by
  constructor
  · left; unfold rightArg; omega
  · intro p h; simp only [rightArg,leftCell,rightCell]; omega

theorem leftCell_le (p : ℕ) : leftCell p ≤ -6 := by unfold leftCell; omega
theorem rightCell_le (p : ℕ) : rightCell p ≤ -6 := by unfold rightCell; omega
theorem leftCell_inj : Function.Injective leftCell := by intro i j h; unfold leftCell at h; omega
theorem rightCell_inj : Function.Injective rightCell := by intro i j h; unfold rightCell at h; omega
theorem cells_distinct (i j : ℕ) : leftCell i ≠ rightCell j := by unfold leftCell rightCell; omega

theorem digit_val {n t : ℕ} (x : Fin (n^t)) (p : Fin t) :
    (digit x p).val = x.val/n^p.val%n := rfl

def Shape.packed (t k : ℕ) (s : Shape) : Command :=
  .seq (.atom (.one Reg.one))
  (.seq (Digits.unpack (leftArg t) leftCell t)
  (.seq (Digits.unpack (rightArg t) rightCell t) (s.command (t:=t) k)))

def Shape.packedCost {n t : ℕ} (k : ℕ) (s : Shape) (x y : Fin (n^t)) : ℕ :=
  1+((1+Digits.cost n x.val t)+((1+Digits.cost n y.val t)+s.cost k x y))

theorem packedCost_le {n t : ℕ} (k : ℕ) (s : Shape) (x y : Fin (n^t)) :
    s.packedCost k x y ≤ 5 + (t+t*t)*8 + 2*(t*(5+5*n^t)) := by
  have hx := (Digits.cost_le n x.val t).trans (Nat.mul_le_mul_left t
    (show 5+5*x.val ≤ 5+5*n^t by have := x.isLt; omega))
  have hy := (Digits.cost_le n y.val t).trans (Nat.mul_le_mul_left t
    (show 5+5*y.val ≤ 5+5*n^t by have := y.isLt; omega))
  have hw := cost_le k s x y
  unfold Shape.packedCost
  omega

/-- The packed entry point. The input graph is in its published nonnegative
cells, while the two compact integer labels are in fixed negative cells chosen
by t. All decoding, comparisons and adjacency probes are charged. -/
theorem packed_runs {b n t : ℕ} (hb : t+4 ≤ b) (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (k : ℕ) (s : Shape) (x y : Fin (n^t)) {m : Memory} (gr : GraphAt G m)
    (hx : m (leftArg t) = (x.val:ℤ)) (hy : m (rightArg t) = (y.val:ℤ)) :
    ∃ out, Runs (b*(n.log2+1)) (s.packed t k) m (s.packedCost k x y) out ∧
      (out Reg.acc : ℚ) = weights G k ⟨0,hn⟩ (s.key x y) ∧
      ∀ z, Kept t z → out z=m z := by
  let W := b*(n.log2+1)
  let m₀ := update m Reg.one 1
  have initial : Runs W (.atom (.one Reg.one)) m 1 m₀ := .atom (.one _ _)
  have keep₀ (z : ℤ) (hz : z≤ -6 ∨ 0≤z) : m₀ z=m z := by
    have h : z≠Reg.one := by rcases hz with h|h <;> change z≠ -5 <;> omega
    simp [m₀,update,h]
  have hconst : m₀ Division.one=1 := by simp [m₀,update,Division.one,Reg.one]
  have hn₀ : m₀ 0=n := (keep₀ _ (Or.inr le_rfl)).trans gr.1
  have hleft : m₀ (leftArg t) = (x.val:ℤ) := (keep₀ _ (kept_leftArg t).1).trans hx
  have hright : m₀ (rightArg t) = (y.val:ℤ) := (keep₀ _ (kept_rightArg t).1).trans hy
  have cap : Division.Room W (n^(t+1)) := Division.room_pow hn (by omega)
  have hN : n ≤ n^(t+1) := by simpa using Nat.pow_le_pow_right hn (show 1≤t+1 by omega)
  have hbig : n^t ≤ n^(t+1) := Nat.pow_le_pow_right hn (by omega)
  obtain ⟨m₁,act₁,d₁,keep₁⟩ := Digits.unpack_runs hn cap hN (x.isLt.le.trans hbig) m₀ hn₀ hconst
    (leftArg t) hleft leftCell leftCell_le leftCell_inj t
  have protect (z : ℤ) (hz : z≤ -6 ∨ 0≤z) : Protected z := hz.imp (fun h => by omega) id
  have same₁ (z : ℤ) (hz : Kept t z) : m₁ z=m₀ z :=
    keep₁ z (protect _ hz.1) (fun p hp => (hz.2 p hp).1)
  have const₁ : m₁ Division.one=1 := (keep₁ _ (Or.inl (by decide : Division.one≤ -5))
    (fun p _ => by have := leftCell_le p; change -5≠leftCell p; omega)).trans hconst
  have hn₁ := (same₁ _ (kept_nonneg le_rfl t)).trans hn₀
  have arg₁ := (same₁ _ (kept_rightArg t)).trans hright
  obtain ⟨m₂,act₂,d₂,keep₂⟩ := Digits.unpack_runs hn cap hN (y.isLt.le.trans hbig) m₁ hn₁ const₁
    (rightArg t) arg₁ rightCell rightCell_le rightCell_inj t
  have same₂ (z : ℤ) (hz : Kept t z) : m₂ z=m z :=
    ((keep₂ z (protect _ hz.1) (fun p hp => (hz.2 p hp).2)).trans (same₁ z hz)).trans
      (keep₀ z hz.1)
  have graph : GraphAt G m₂ := ⟨(same₂ _ (kept_nonneg le_rfl t)).trans gr.1, fun u v =>
    (same₂ _ (kept_nonneg (Int.natCast_nonneg _) t)).trans (gr.2 u v)⟩
  have data (i : Side t) : m₂ (digitRegister i)=(digits x y i).val := by
    cases i with
    | inl p =>
      change m₂ (leftCell p.val) = ((digit x p).val:ℤ)
      rw [digit_val]
      exact (keep₂ _ (Or.inl (by have := leftCell_le p.val; omega))
        (fun q _ => cells_distinct p.val q)).trans (d₁ p.val p.isLt)
    | inr p =>
      change m₂ (rightCell p.val) = ((digit y p).val:ℤ)
      rw [digit_val]
      exact d₂ p.val p.isLt
  obtain ⟨out,run,val,fr⟩ := weight_runs hn G k s x y graph (graphCapacity (by omega : 4≤b) hn) data
  exact ⟨out,.seq initial (.seq act₁ (.seq act₂ run)),val,fun z hz => (fr z hz.1).trans (same₂ z hz)⟩

end VWZClique.IntegerRAM.Graph
end

/- WordGraphCursor -/
section
namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

inductive Cell where
  | x | y | ptr | unit | cols | lim | index | flag
  deriving DecidableEq

def cell (t : ℕ) : Cell → ℤ
  | .x => leftArg t
  | .y => rightArg t
  | .ptr => -10-2*(t:ℤ)
  | .unit => -11-2*(t:ℤ)
  | .cols => -12-2*(t:ℤ)
  | .lim => -13-2*(t:ℤ)
  | .index => -14-2*(t:ℤ)
  | .flag => -15-2*(t:ℤ)

theorem cell_below (t : ℕ) (c : Cell) : cell t c≤ -8 := by
  cases c <;> simp only [cell,leftArg,rightArg] <;> omega

@[simp] theorem cell_eq {t : ℕ} {a b : Cell} : cell t a=cell t b ↔ a=b := by
  constructor
  · intro h
    cases a <;> cases b <;> simp_all [cell,leftArg,rightArg] <;> omega
  · exact congrArg _

@[simp] theorem nat_ne_cell (t k : ℕ) (c : Cell) : (k:ℤ) ≠ cell t c := by
  have := cell_below t c; omega

@[simp] theorem cell_ne_nat (t k : ℕ) (c : Cell) : cell t c ≠ (k:ℤ) := (nat_ne_cell t k c).symm

@[simp] theorem zero_ne_cell (t : ℕ) (c : Cell) : 0 ≠ cell t c := nat_ne_cell t 0 c

theorem cell_kept (t : ℕ) (c : Cell) : Kept t (cell t c) := by
  constructor
  · left; have := cell_below t c; omega
  · intro p h; cases c <;> simp only [cell,leftArg,rightArg,leftCell,rightCell] <;> omega

/-- Register contents between consecutive positions in the same shape's table. -/
structure Controls (t C N p x y q : ℕ) (m : Memory) : Prop where
  unit : m (cell t .unit)=1
  cols : m (cell t .cols)=C
  lim : m (cell t .lim)=N
  ptr : m (cell t .ptr)=p
  x : m (cell t .x)=x
  y : m (cell t .y)=y
  index : m (cell t .index)=q

theorem Controls.transfer {t C N p x y q : ℕ} {a b : Memory} (h : Controls t C N p x y q a)
    (eqs : ∀ c, b (cell t c)=a (cell t c)) : Controls t C N p x y q b :=
  ⟨(eqs _).trans h.unit,(eqs _).trans h.cols,(eqs _).trans h.lim,
   (eqs _).trans h.ptr,(eqs _).trans h.x,(eqs _).trans h.y,(eqs _).trans h.index⟩

def carry (t : ℕ) : Command :=
  .seq (.atom (.sub (cell t .y) (cell t .y) (cell t .y)))
    (.atom (.add (cell t .x) (cell t .x) (cell t .unit)))

def advance (t : ℕ) : Command :=
  .seq (.atom (.store (cell t .ptr) Reg.acc))
  (.seq (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit)))
  (.seq (.atom (.add (cell t .y) (cell t .y) (cell t .unit)))
  (.seq (.atom (.sub (cell t .flag) (cell t .y) (cell t .cols)))
        (.whenNonnegative (cell t .flag) (carry t)))))

def xNext (C x y : ℕ) := if y+1<C then x else x+1
def yNext (C y : ℕ) := if y+1<C then y+1 else 0

theorem advance_runs {W M t C N p x y q : ℕ} {m : Memory}
    (r : Controls t C N p x y q m) (hy : y<C) (hp : p≤M) (hc : C≤M)
    (room : Division.Room W M) :
    ∃ out, Runs W (advance t) m (4+(if y+1<C then 1 else 3)) out ∧
      Controls t C N (p+1) (xNext C x y) (yNext C y) q out ∧
      ∀ z : ℕ, out (z:ℤ) = if z=p then m Reg.acc else m z := by
  let a := update m (p:ℤ) (m Reg.acc)
  let b := update a (cell t .ptr) ((p:ℤ)+1)
  let c := update b (cell t .y) ((y:ℤ)+1)
  let d := update c (cell t .flag) ((y:ℤ)+1-C)
  have pa : Fits W (m (cell t .ptr)) := by rw [r.ptr]; apply room.fits <;> omega
  have first : Runs W (.atom (.store (cell t .ptr) Reg.acc)) m 1 a := by
    simpa only [a,r.ptr] using Runs.atom (Step.store m (cell t .ptr) Reg.acc pa)
  have ra : Controls t C N p x y q a := r.transfer (fun i => by simp [a,update])
  have second : Runs W (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))) a 1 b := by
    simpa only [b,ra.ptr,ra.unit] using Runs.atom (Step.add (W:=W) a (cell t .ptr) (cell t .ptr) (cell t .unit))
  have third : Runs W (.atom (.add (cell t .y) (cell t .y) (cell t .unit))) b 1 c := by
    simpa [b,c,update,ra.y,ra.unit] using Runs.atom (Step.add (W:=W) b (cell t .y) (cell t .y) (cell t .unit))
  have fourth : Runs W (.atom (.sub (cell t .flag) (cell t .y) (cell t .cols))) c 1 d := by
    simpa [d,c,b,update,ra.cols] using Runs.atom (Step.sub (W:=W) c (cell t .flag) (cell t .y) (cell t .cols))
  have dt : d (cell t .flag) = (y:ℤ)+1-C := by simp [d,update]
  have hd : Fits W (d (cell t .flag)) := by rw [dt]; apply room.fits <;> omega
  have cin : Controls t C N (p+1) x (y+1) q d := by
    constructor <;> simp [d,c,b,update,ra.unit,ra.cols,ra.lim,ra.ptr,ra.x,ra.index]
  have data (z : ℕ) : d z = if z=p then m Reg.acc else m z := by
    simp [d,c,b,a,update]
  by_cases small : y+1<C
  · refine ⟨d,?_,by simpa [xNext,yNext,small] using cin,data⟩
    have branch := Runs.guard_skip (c:=carry t) hd (show d (cell t .flag)<0 by omega)
    simpa [advance,small] using Runs.seq first (.seq second (.seq third (.seq fourth branch)))
  · let e := update d (cell t .y) 0
    let f := update e (cell t .x) ((x:ℤ)+1)
    have c₁ : Runs W (.atom (.sub (cell t .y) (cell t .y) (cell t .y))) d 1 e := by
      simpa [e] using Runs.atom (Step.sub (W:=W) d (cell t .y) (cell t .y) (cell t .y))
    have c₂ : Runs W (.atom (.add (cell t .x) (cell t .x) (cell t .unit))) e 1 f := by
      simpa [e,f,update,cin.x,cin.unit] using Runs.atom (Step.add (W:=W) e (cell t .x) (cell t .x) (cell t .unit))
    have branch := Runs.guard_take (c:=carry t) hd (show ¬ d (cell t .flag)<0 by omega) (.seq c₁ c₂)
    refine ⟨f,?_,?_,?_⟩
    · simpa [advance,small] using Runs.seq first (.seq second (.seq third (.seq fourth branch)))
    · constructor <;> simp [xNext,yNext,small,e,f,update,cin.unit,cin.cols,cin.lim,cin.ptr,cin.index]
    · intro z
      simpa [f,e,update] using data z

theorem Controls.tick {t C N p x y q : ℕ} {m : Memory} (h : Controls t C N p x y q m) :
    Controls t C N p x y (q+1) (nextMemory m (cell t .index) (cell t .flag) q N) := by
  constructor <;> simp [nextMemory,update,h.unit,h.cols,h.lim,h.ptr,h.x,h.y]

theorem tick_data (t q N z : ℕ) (m : Memory) :
    nextMemory m (cell t .index) (cell t .flag) q N (z:ℤ)=m z := by simp [nextMemory,update]

end VWZClique.IntegerRAM.Graph.Table
end

/- WordGraphSetup -/
section
namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

def columns (s : Shape) (N : ℕ) : ℕ := match s with
  | .unary _ => 1
  | .cross _ _ => N

theorem cols_le (s : Shape) {N : ℕ} (h : 0<N) : columns s N ≤ N := by cases s <;> simp [columns] <;> omega
theorem cols_pos (s : Shape) {N : ℕ} (h : 0<N) : 0<columns s N := by cases s <;> simp [columns,h]

private theorem overwrite (m : Memory) (d u v : ℤ) : update (update m d u) d v=update m d v := by
  funext z; by_cases h:z=d <;> simp [update,h]

def power (t : ℕ) : ℕ → Command
  | 0 => .atom (.one (cell t .lim))
  | j+1 => .seq (power t j) (.atom (.mul (cell t .lim) (cell t .lim) 0))

theorem power_runs (W t j : ℕ) (m : Memory) :
    Runs W (power t j) m (j+1) (update m (cell t .lim) (m 0 ^ j)) := by
  induction j with
  | zero => simpa [power] using Runs.atom (Step.one (W:=W) m (cell t .lim))
  | succ j ih =>
    let z := update m (cell t .lim) (m 0^j)
    have act := Runs.atom (Step.mul (W:=W) z (cell t .lim) (cell t .lim) 0)
    have hl : z (cell t .lim)=m 0 ^ j := by simp [z,update]
    have hd : z 0=m 0 := by simp [z,update]
    rw [hl,hd,←pow_succ] at act
    simpa only [power,z,overwrite] using Runs.seq ih act

def colCode (t : ℕ) : Shape → Command
  | .unary _ => .atom (.one (cell t .cols))
  | .cross _ _ => .atom (.mul (cell t .cols) (cell t .lim) (cell t .unit))

theorem colCode_runs {W t N : ℕ} (s : Shape) {m : Memory}
    (hl : m (cell t .lim)=(N:ℤ)) (hu : m (cell t .unit)=1) :
    Runs W (colCode t s) m 1 (update m (cell t .cols) (columns s N)) := by
  cases s with
  | unary i => simpa [colCode,columns] using Runs.atom (Step.one (W:=W) m (cell t .cols))
  | cross i j =>
    simpa [colCode,columns,hl,hu] using Runs.atom (Step.mul (W:=W) m (cell t .cols) (cell t .lim) (cell t .unit))

def zeroCell (d : ℤ) : Command := .atom (.sub d d d)

theorem zeroCell_runs (W : ℕ) (m : Memory) (d : ℤ) :
    Runs W (zeroCell d) m 1 (update m d 0) := by simpa [zeroCell] using Runs.atom (Step.sub (W:=W) m d d d)

def setup (t : ℕ) (s : Shape) : Command :=
  .seq (.atom (.one (cell t .unit)))
  (.seq (power t t)
  (.seq (colCode t s)
  (.seq (.atom (.mul (cell t .lim) (cell t .lim) (cell t .cols)))
  (.seq (zeroCell (cell t .x)) (.seq (zeroCell (cell t .y)) (zeroCell (cell t .index)))))))

theorem setup_runs {W n t base : ℕ} (s : Shape) (m : Memory) (hd : m 0=n)
    (hp : m (cell t .ptr)=base) :
    ∃ out, Runs W (setup t s) m (t+7) out ∧
      Controls t (columns s (n^t)) ((n^t)*columns s (n^t)) base 0 0 0 out ∧
      ∀ z : ℕ, out z=m z := by
  let N := n^t
  let C := columns s N
  let u := update m (cell t .unit) 1
  let v := update u (cell t .lim) (N:ℤ)
  let w := update v (cell t .cols) (C:ℤ)
  let x := update w (cell t .lim) ((N*C:ℕ):ℤ)
  let y := update x (cell t .x) 0
  let z := update y (cell t .y) 0
  let f := update z (cell t .index) 0
  have op₁ : Runs W (.atom (.one (cell t .unit))) m 1 u := .atom (.one _ _)
  have op₂ : Runs W (power t t) u (t+1) v := by
    have h0 : u 0=n := by simpa [u,update] using hd
    simpa only [v,N,Nat.cast_pow,h0] using power_runs W t t u
  have op₃ : Runs W (colCode t s) v 1 w := by
    apply colCode_runs (N:=N) <;> simp [v,u,update]
  have op₄ : Runs W (.atom (.mul (cell t .lim) (cell t .lim) (cell t .cols))) w 1 x := by
    simpa [x,w,v,update] using Runs.atom (Step.mul (W:=W) w (cell t .lim) (cell t .lim) (cell t .cols))
  have run := Runs.seq op₁ (.seq op₂ (.seq op₃ (.seq op₄
    (.seq (zeroCell_runs W x (cell t .x)) (.seq (zeroCell_runs W y (cell t .y)) (zeroCell_runs W z (cell t .index)))))))
  refine ⟨f,?_,?_,?_⟩
  · simpa only [setup,show 1+((t+1)+(1+(1+(1+(1+1)))))=t+7 by omega] using run
  · constructor <;> simp [f,z,y,x,w,v,u,update,hp,N,C]
  · intro i; simp [f,z,y,x,w,v,u,update]

end VWZClique.IntegerRAM.Graph.Table
end

/- WordGraphBlock -/
section
namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

theorem address_lt_headerEnd {n : ℕ} (u v : Fin n) :
    1+u.val*n+v.val < 1+n*n := by
  have h := Nat.mul_le_mul_right n u.isLt
  rw [Nat.succ_mul] at h
  have := v.isLt
  omega

theorem GraphAt_before {n base : ℕ} {G : SimpleGraph (Fin n)} {m out : Memory}
    (h : GraphAt G m) (hb : 1+n*n≤base) (fr : ∀ z : ℕ, z<base → out z=m z) : GraphAt G out := by
  refine ⟨(fr 0 (by omega)).trans h.1,fun u v => ?_⟩
  exact (fr _ ((address_lt_headerEnd u v).trans_le hb)).trans (h.2 u v)

def entryBound (t N : ℕ) := 5+(t+t*t)*8+2*(t*(5+5*N))
def blockBound (t N C : ℕ) := (t+7) + (N*C)*(entryBound t N+10)

def block (t k : ℕ) (s : Shape) : Command :=
  .seq (setup t s) (repeatN (.seq (s.packed t k) (advance t))
    (cell t .index) (cell t .unit) (cell t .lim) (cell t .flag))

noncomputable def Value {n t : ℕ} (G : SimpleGraph (Fin n)) (hn : 1≤n) (k : ℕ) (s : Shape)
    (x y : Fin (n^t)) : ℚ := weights G k ⟨0,hn⟩ (s.key x y)

private theorem coords_unique {w a b c d : ℕ} (hw : 0<w) (hb : b<w) (hd : d<w)
    (h : a*w+b=c*w+d) : a=c ∧ b=d := by
  have div (u v : ℕ) (hv : v<w) : (u*w+v)/w=u := by
    rw [Nat.mul_comm,Nat.mul_add_div hw,Nat.div_eq_of_lt hv,Nat.add_zero]
  have modn (u v : ℕ) (hv : v<w) : (u*w+v)%w=v := by
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt hv]
  exact ⟨(div a b hb).symm.trans ((congrArg (·/w) h).trans (div c d hd)),
    (modn a b hb).symm.trans ((congrArg (·%w) h).trans (modn c d hd))⟩

/-- One contiguous unary (N words) or ordered-pair (N² words) table.
The input pointer can follow previously computed tables. -/
theorem block_runs {b n t base M : ℕ} (hb : t+4≤b) (hn : 1≤n)
    (G : SimpleGraph (Fin n)) (k : ℕ) (s : Shape) (m : Memory) (gr : GraphAt G m)
    (hp : m (cell t .ptr)=base) (separate : 1+n*n≤base)
    (room : Division.Room (b*(n.log2+1)) M) (fits : base+n^t*columns s (n^t)≤M) :
    ∃ T, T≤blockBound t (n^t) (columns s (n^t)) ∧ ∃ out,
      Runs (b*(n.log2+1)) (block t k s) m T out ∧
      out (cell t .ptr)=((base+n^t*columns s (n^t):ℕ):ℤ) ∧
      (∀ x y : Fin (n^t), y.val<columns s (n^t) →
        (out ((base+x.val*columns s (n^t)+y.val:ℕ):ℤ) : ℚ)=Value G hn k s x y) ∧
      ∀ z : ℕ, z<base ∨ base+n^t*columns s (n^t)≤z → out z=m z := by
  let W := b*(n.log2+1)
  let N := n^t
  let C := columns s N
  let D := N*C
  have hN : 0<N := Nat.pow_pos hn
  have hC : 0<C := cols_pos s hN
  have hCN : C≤N := cols_le s hN
  have hD : 0<D := Nat.mul_pos hN hC
  have hcap : base+D≤M := fits
  have hCM : C≤M := by
    have hh : C≤D := by simpa [D] using Nat.mul_le_mul_right C hN
    omega
  let inv := fun (j : ℕ) (a : Memory) => ∃ u v : ℕ,
    u*C+v=j ∧ v<C ∧ Controls t C D (base+j) u v j a ∧
    (∀ x y : Fin (n^t), y.val<C → x.val*C+y.val<j →
      (a ((base+x.val*C+y.val:ℕ):ℤ) : ℚ)=Value G hn k s x y) ∧
    ∀ z : ℕ, z<base ∨ base+j≤z → a z=m z
  obtain ⟨m₀,start,ctl₀,same₀⟩ := setup_runs (W:=W) s m gr.1 hp
  have init : inv 0 m₀ := ⟨0,0,by simp,hC,by simpa using ctl₀,by omega,fun z _ => same₀ z⟩
  have fitGuard (q : ℕ) (hq : q≤D) : Fits W ((q:ℤ)-D) := by apply room.fits <;> omega
  have action (q : ℕ) (hq : q<D) (a : Memory) (hin : inv q a) :
      ∃ T : ℕ, T≤entryBound t N+7 ∧ ∃ out : Memory,
        Runs W (.seq (s.packed t k) (advance t)) a T out ∧
        out (cell t .index)=q ∧ out (cell t .unit)=1 ∧ out (cell t .lim)=D ∧
        inv (q+1) (nextMemory out (cell t .index) (cell t .flag) q D) := by
    obtain ⟨u,v,loc,vc,ctl,previous,same⟩ := hin
    have un : u<N := by
      by_contra! bad
      have := Nat.mul_le_mul_right C bad
      omega
    let x : Fin (n^t) := ⟨u,un⟩
    let y : Fin (n^t) := ⟨v,vc.trans_le hCN⟩
    have ga : GraphAt G a := GraphAt_before gr separate (fun z hz => same z (Or.inl hz))
    obtain ⟨v₀,weight,ans,saved⟩ := packed_runs hb hn G k s x y ga ctl.x ctl.y
    have ctl' := ctl.transfer (fun c => saved _ (cell_kept t c))
    obtain ⟨a₁,act,nxt,write⟩ := advance_runs ctl' vc (by omega : base+q≤M) hCM room
    have Tbound := packedCost_le k s x y
    have stepB : s.packedCost k x y + (4+(if v+1<C then 1 else 3)) ≤ entryBound t N+7 := by
      change s.packedCost k x y ≤ entryBound t N at Tbound
      split <;> omega
    refine ⟨_,stepB,a₁,.seq weight act,nxt.index,nxt.unit,nxt.lim,?_⟩
    have nextloc : xNext C u v*C+yNext C v=q+1 := by
      by_cases h : v+1<C <;> simp [xNext,yNext,h,Nat.add_mul] <;> omega
    have nextlt : yNext C v<C := by by_cases h:v+1<C <;> simp [yNext,h,hC]
    let a₂ := nextMemory a₁ (cell t .index) (cell t .flag) q D
    have new (z : ℕ) : a₂ z = if z=base+q then v₀ Reg.acc else a z := by
      rw [show a₂ z=a₁ z from tick_data t q D z a₁,write]
      by_cases h : z=base+q <;> simp [h,saved _ (kept_nonneg (Int.natCast_nonneg z) t)]
    change inv (q+1) a₂
    refine ⟨_,_,nextloc,nextlt,by simpa only [Nat.add_assoc] using nxt.tick,?_,?_⟩
    · intro i j hj hlt
      by_cases old : i.val*C+j.val<q
      · rw [new,if_neg (by omega)]
        exact previous i j hj old
      · obtain ⟨hi,hj'⟩ := coords_unique hC hj vc (show i.val*C+j.val=u*C+v by omega)
        have ei : i=x := Fin.ext hi
        have ej : j=y := Fin.ext hj'
        rw [new,if_pos (by omega),ei,ej]
        exact ans
    · intro z hz
      rw [new,if_neg (by omega)]
      exact same z (by omega)
  obtain ⟨fuel,time,out,run,done⟩ := repeatN_runs (W:=W) (B:=entryBound t N+7) hD _
    (by simp : cell t .lim ≠ cell t .index) inv fitGuard action init
  obtain ⟨_,_,_,_,ctl,all,same⟩ := done
  refine ⟨(t+7)+fuel,?_,out,.seq start run,ctl.ptr,?_,same⟩
  · change (t+7)+fuel ≤ (t+7) + D*(entryBound t N+10)
    exact Nat.add_le_add_left (by simpa only [Nat.add_assoc] using time) _
  · intro x y hy
    change y.val<C at hy
    apply all x y hy
    have hx : (x.val+1)*C≤N*C := Nat.mul_le_mul_right _ x.isLt
    rw [Nat.add_mul,one_mul] at hx
    change x.val*C+y.val < N*C
    omega

end VWZClique.IntegerRAM.Graph.Table
end

/- WordGraphSchedule -/
section
namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

def vertex (i : ℕ) : V := ⟨i%9,Nat.mod_lt _ (by decide)⟩

/-- The nine unary tables come first, followed by the 81 ordered edge tables. -/
def shapeAt (j : ℕ) : Shape :=
  if j<9 then .unary (vertex j) else .cross (vertex ((j-9)/9)) (vertex (j-9))

theorem unaryAt (i : V) : shapeAt i.val=.unary i := by
  simp only [shapeAt,if_pos i.isLt]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem crossAt (i j : V) : shapeAt (9+i.val*9+j.val)=.cross i j := by
  have h : 9+i.val*9+j.val-9=i.val*9+j.val := by omega
  have hdiv : (i.val*9+j.val)/9=i.val := by
    rw [Nat.mul_comm,Nat.mul_add_div (by decide : 0<9),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hmod : (i.val*9+j.val)%9=j.val := by
    rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  simp only [shapeAt,if_neg (by omega : ¬9+i.val*9+j.val<9), h,hdiv]
  congr 1
  · exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  · exact Fin.ext hmod

def offset (N j : ℕ) : ℕ := min j 9 * N + (j-9)*(N*N)

theorem offset_succ (N j : ℕ) :
    offset N (j+1) = offset N j + N*columns (shapeAt j) N := by
  by_cases h : j<9
  · simp only [offset,min_eq_left (by omega : j+1≤9),min_eq_left h.le,
      Nat.sub_eq_zero_of_le (by omega : j+1≤9),Nat.sub_eq_zero_of_le h.le,zero_mul,
      Nat.add_zero,shapeAt,if_pos h,columns,mul_one,add_mul,one_mul]
  · have d : j+1-9=(j-9)+1 := by omega
    simp only [offset,min_eq_right (by omega : 9≤j+1),min_eq_right (by omega : 9≤j),
      d,shapeAt,if_neg h,columns]
    ring

theorem offset_mono (N : ℕ) : Monotone (offset N) := by
  intro i j hij
  exact Nat.add_le_add (Nat.mul_le_mul_right N (min_le_min_right 9 hij))
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hij 9))

def schedule (t k : ℕ) : ℕ → Command
  | 0 => .skip
  | j+1 => .seq (schedule t k j) (block t k (shapeAt j))

theorem index_lt (N C : ℕ) (x y : Fin N) (hy : y.val<C) : x.val*C+y.val<N*C := by
  have h := Nat.mul_le_mul_right C x.isLt
  rw [Nat.succ_mul] at h
  omega

/-- Prefix of the fixed-size schedule. Table values use both row-major indices
inside each edge table. Earlier completed tables survive all subsequent passes. -/
theorem schedule_runs {b n t base M : ℕ} (hb : t+4≤b) (hn : 1≤n)
    (G : SimpleGraph (Fin n)) (k : ℕ) (m : Memory) (gr : GraphAt G m)
    (hp : m (cell t .ptr)=base) (separate : 1+n*n≤base)
    (room : Division.Room (b*(n.log2+1)) M) (L : ℕ) (fits : base+offset (n^t) L≤M) :
    ∃ T, T≤L*blockBound t (n^t) (n^t) ∧ ∃ out,
      Runs (b*(n.log2+1)) (schedule t k L) m T out ∧
      out (cell t .ptr)=((base+offset (n^t) L:ℕ):ℤ) ∧
      (∀ j<L, ∀ x y : Fin (n^t), y.val<columns (shapeAt j) (n^t) →
        (out ((base+offset (n^t) j+x.val*columns (shapeAt j) (n^t)+y.val:ℕ):ℤ) : ℚ)=
          Value G hn k (shapeAt j) x y) ∧
      ∀ z : ℕ, z<base ∨ base+offset (n^t) L≤z → out z=m z := by
  let N := n^t
  have hN : 0<N := Nat.pow_pos hn
  induction L with
  | zero => exact ⟨0,by simp,m,.skip _,by simpa [offset] using hp,by omega,fun _ _ => rfl⟩
  | succ j ih =>
    have prevFit : base+offset N j≤M := (Nat.add_le_add_left (offset_mono N (Nat.le_succ j)) _).trans fits
    obtain ⟨f,tf,x,prior,ptr,old,stable⟩ := ih prevFit
    have graph : GraphAt G x := GraphAt_before gr separate (fun z hz => stable z (Or.inl hz))
    have nextFit : (base+offset N j) + N*columns (shapeAt j) N≤M := by
      rw [Nat.add_assoc,←offset_succ]
      exact fits
    obtain ⟨g,tg,out,now,ptr',done,next⟩ := block_runs hb hn G k (shapeAt j) x graph ptr
      (by omega : 1+n*n≤base+offset N j) room nextFit
    have hb' : blockBound t N (columns (shapeAt j) N)≤blockBound t N N := by
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left N (cols_le _ hN))
    refine ⟨f+g,?_,out,.seq prior now,?_,?_,?_⟩
    · rw [Nat.succ_mul]
      exact Nat.add_le_add tf (tg.trans hb')
    · simpa only [offset_succ,Nat.add_assoc] using ptr'
    · intro i hi a v hcol
      by_cases last : i=j
      · subst i
        exact done a v hcol
      · have he := offset_mono N (by omega : i+1≤j)
        rw [offset_succ] at he
        have hbnd := index_lt N (columns (shapeAt i) N) a v hcol
        have addr : base+offset N i+a.val*columns (shapeAt i) N+v.val < base+offset N j := by omega
        rw [next _ (Or.inl addr)]
        exact old i (by omega) a v hcol
    · intro z hz
      rw [offset_succ] at hz
      rw [next z (by omega),stable z (by omega)]

def baseCommand (t : ℕ) : Command :=
  .seq (.atom (.one (cell t .unit)))
  (.seq (.atom (.mul (cell t .ptr) 0 0))
        (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))))

theorem base_runs {W n : ℕ} (t : ℕ) (m : Memory) (hn : m 0=n) :
    ∃ out, Runs W (baseCommand t) m 3 out ∧ out (cell t .ptr)=((1+n*n:ℕ):ℤ) ∧
      ∀ z : ℕ, out z=m z := by
  let x := update m (cell t .unit) 1
  let y := update x (cell t .ptr) ((n:ℤ)*n)
  let out := update y (cell t .ptr) (((n:ℤ)*n)+1)
  have h₁ : Runs W (.atom (.one (cell t .unit))) m 1 x := .atom (.one _ _)
  have h₂ : Runs W (.atom (.mul (cell t .ptr) 0 0)) x 1 y := by
    simpa [x,y,update,hn] using Runs.atom (Step.mul (W:=W) x (cell t .ptr) 0 0)
  have h₃ : Runs W (.atom (.add (cell t .ptr) (cell t .ptr) (cell t .unit))) y 1 out := by
    simpa [y,x,out,update] using Runs.atom (Step.add (W:=W) y (cell t .ptr) (cell t .ptr) (cell t .unit))
  refine ⟨out,.seq h₁ (.seq h₂ h₃),?_,?_⟩
  · simp [out,update,add_comm]
  · intro z; simp [out,y,x,update]

end VWZClique.IntegerRAM.Graph.Table
end

/- WordGraphTable -/
section
/-! A native tabulator, on the graph alone, for every blocked zero-one weight.
It writes its 9N+81N² results immediately after the adjacency input. -/

namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction
open TrulySubcubicAPSP

def coefficient (t : ℕ) := 4+90*((t+7)+(15+(t+t*t)*8+20*t))
def machine (t k : ℕ) := Command.seq (baseCommand t) (schedule t k 90)

theorem table_capacity {n : ℕ} (hn : 2≤n) (t : ℕ) :
    1+n*n+offset (n^t) 90 ≤ n^(2*t+9) := by
  let A := n^(2*t+2)
  have hn1 : 1≤n := by omega
  have h1 : 1 ≤ A := Nat.one_le_pow _ _ hn1
  have h2 : n*n ≤ A := by
    rw [←sq]
    exact Nat.pow_le_pow_right hn1 (by omega)
  have hN : n^t ≤ A := Nat.pow_le_pow_right hn1 (by omega)
  have hN₂ : n^t*n^t ≤ A := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right hn1 (by omega)
  have h92 : 92≤n^7 := (by decide : 92≤2^7).trans (Nat.pow_le_pow_left hn 7)
  calc
    _ = 1+n*n+(9*n^t+81*(n^t*n^t)) := by norm_num [offset]
    _ ≤ 92*A := by omega
    _ ≤ n^7*A := Nat.mul_le_mul_right A h92
    _ = _ := by dsimp [A]; rw [←pow_add]; congr 1; omega

theorem table_cubic {N : ℕ} (hN : 1≤N) (t : ℕ) :
    4+90*blockBound t N N ≤ coefficient t*N^3 := by
  let A := 15+(t+t*t)*8+10*t
  let B := 15+(t+t*t)*8+20*t
  have hA : A≤A*N := by simpa using Nat.mul_le_mul_left A hN
  have entry : entryBound t N+10 ≤ B*N := by
    calc
      _ = A+(10*t)*N := by dsimp [entryBound,A]; ring
      _ ≤ A*N+(10*t)*N := Nat.add_le_add_right hA _
      _ = _ := by dsimp [A,B]; ring
  have hn3 : 1≤N^3 := Nat.one_le_pow _ _ hN
  have setup : t+7 ≤ (t+7)*N^3 := by simpa using Nat.mul_le_mul_left (t+7) hn3
  have per : blockBound t N N ≤ (t+7+B)*N^3 := by
    calc
      _ ≤ (t+7)*N^3+(N*N)*(B*N) := Nat.add_le_add setup (Nat.mul_le_mul_left _ entry)
      _ = _ := by ring
  have hc : 4≤4*N^3 := by simpa using Nat.mul_le_mul_left 4 hn3
  calc
    _ ≤ 4*N^3+90*((t+7+B)*N^3) := Nat.add_le_add hc (Nat.mul_le_mul_left _ per)
    _ = _ := by unfold coefficient B; ring

/-- Compile one fixed program per t,k and fill all unary and edge arrays,
starting with exactly the original graph memory. This includes the time to
derive N, the input length, all counters, and all radix and adjacency probes. -/
theorem preprocess_runs {n : ℕ} (hn : 2≤n) (G : SimpleGraph (Fin n)) (t k : ℕ) :
    ∃ T, T+1≤coefficient t*(n^t)^3 ∧ ∃ out,
      Runs ((2*t+11)*(n.log2+1)) (machine t k) (input (MonDepMW.graphInput G)) T out ∧
      (∀ a : WeightKey (n^t), (out (((MonDepMW.graphInput G).length+wordIndex a:ℕ):ℤ) : ℚ)=
        weights G k ⟨0,by omega⟩ a) ∧
      ∀ j<(MonDepMW.graphInput G).length, out (j:ℤ)=input (MonDepMW.graphInput G) j := by
  let W := (2*t+11)*(n.log2+1)
  let N := n^t
  have hn' : 1≤n := by omega
  have hN : 1≤N := Nat.one_le_pow _ _ hn'
  let m := input (MonDepMW.graphInput G)
  have graph : GraphAt G m := graphAt_input G
  obtain ⟨m₀,base,ptr,keep⟩ := base_runs (W:=W) t m graph.1
  have g₀ : GraphAt G m₀ := ⟨(keep 0).trans graph.1,fun u v =>
    (keep (1+u.val*n+v.val)).trans (graph.2 u v)⟩
  have room : Division.Room W (n^(2*t+9)) := Division.room_pow hn' (by omega)
  obtain ⟨f,time,out,run,_,all,fr⟩ := schedule_runs (b:=2*t+11) (by omega) hn' G k m₀ g₀ ptr
    le_rfl room 90 (table_capacity hn t)
  refine ⟨3+f,?_,out,.seq base run,?_,?_⟩
  · exact (by omega : 3+f+1≤4+90*blockBound t (n^t) (n^t)).trans (table_cubic hN t)
  · rw [graphInput_length]
    intro a
    rcases a with ⟨i,u⟩|⟨i,j,u,v⟩
    · let z : Fin (n^t) := ⟨0,hN⟩
      have p := all i.val (by have := i.isLt; omega) u z
      rw [unaryAt] at p
      have h := p (by simp [z,columns])
      have off : offset N i.val=i.val*N := by
        simp [offset,min_eq_left i.isLt.le,Nat.sub_eq_zero_of_le i.isLt.le]
      change (out (((1+n*n)+(i.val*N+u.val):ℕ):ℤ) : ℚ)=_
      simpa only [N,off,wordIndex,columns,Nat.mul_one,z,Nat.add_zero,Nat.add_assoc,Value,Shape.key]
        using h
    · let c := 9+i.val*9+j.val
      have hi : i.val<9 := i.isLt
      have hj : j.val<9 := j.isLt
      have c_lt : c<90 := by dsimp [c]; omega
      have p := all c c_lt u v
      rw [show shapeAt c=.cross i j from crossAt i j] at p
      have h := p v.isLt
      have off : offset (n^t) c=9*N+(i.val*9+j.val)*(N*N) := by
        unfold offset
        rw [min_eq_right (by dsimp [c]; omega : 9≤c),show c-9=i.val*9+j.val by dsimp [c]; omega]
      rw [off] at h
      simpa only [Value,columns,Shape.key,N,wordIndex,Nat.add_assoc] using h
  · intro j hj
    rw [graphInput_length] at hj
    exact (fr _ (Or.inl hj)).trans (keep _)

end VWZClique.IntegerRAM.Graph.Table
end

/- NativeFrameStack -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

theorem reset_transition {L W} (lay : StackLayout) (d : ℕ) (hd : d≤36) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b e : Branch) (w : WeightKey (2^L) → ℚ) (i : ℕ) (z : ℤ) (q : List (NativeTraversal.Slot L)) :
    Transition W (Repr lay) (reset d) (.cursor d H π b w i z::q) (.cursor d H π e w 0 z::q) 1 := by
  intro m pre
  obtain ⟨global,⟨wt,prepared,len,_,val⟩,anc⟩ := pre
  obtain ⟨o,run,answer,fr⟩ := reset_runs W d m
  have plane (a : ℕ) (ha:297≤a) := fr (a:ℤ) (distinctData ha hd _)
  have parent (j) (hj:j<d) (k) := fr (reg j k) (ne_of_lt (separate hj _ _))
  have lengths (k : Branch) : o (reg d (lengthField k)) = m (reg d (lengthField k)) :=
    fr _ (different d (by cases k <;> decide))
  exact ⟨1,le_rfl,o,run,global.transfer (fr _ (ne_of_lt (reg_positive d _))) (plane 320 (by decide)) (plane 321 (by decide)),
    ⟨weights_transfer wt (fr _ (different d (by decide))) plane,lay.transferAll _ _ _ _ plane prepared,
    fun k => (lengths k).trans (len k),by simpa using answer,(fr _ (different d (by decide))).trans val⟩,
    saved_transfer lay d q plane parent anc⟩

theorem finish_transition {L W} (lay : StackLayout) (d : ℕ) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b : Branch) (w : WeightKey (2^L) → ℚ) (i : ℕ) (z : ℤ) (q : List (NativeTraversal.Slot L)) :
    Transition W (Repr lay) finish (.cursor d H π b w i z::q) (.value d z::q) 0 := by
  intro m pre
  exact ⟨0,le_rfl,m,.skip _,pre.1,pre.2.1.2.2.2.2,pre.2.2⟩

theorem number_bound (L : ℕ) (H : SimpleGraph V) : number L H ≤ (2^L)^3 := by
  change Fintype.card (RankSwap.Terms L _) ≤ _
  have compact {d : ℕ} : Fintype.card (RankSwap.Terms L d) ≤ 5^L := by
    simpa [RankSwap.MaskEnumeration.Digits] using
      (Fintype.card_le_of_injective _ (RankSwap.MaskEnumeration.code_injective (L:=L) (d:=d)))
  exact compact.trans (RankSwap.MaskEnumeration.scan_range_bound L)

theorem visit_bound (L : ℕ) (H : SimpleGraph V) (b : Branch) : visits (number L H) b ≤ (2^L)^6 := by
  have h := number_bound L H
  have pos : 0<(2^L:ℕ) := by positivity
  have top : (2^L:ℕ)^3 ≤ (2^L)^6 := Nat.pow_le_pow_right pos (by decide)
  cases b with
  | left => exact h.trans top
  | right => exact h.trans top
  | both =>
    calc
      _ ≤ (2^L)^3*(2^L)^3 := Nat.mul_le_mul h h
      _ = _ := by ring

theorem visit_room {W L : ℕ} (H : SimpleGraph V) (b : Branch)
    (cap : Graph.Division.Room W ((2^L)^6)) : Graph.Division.Room W (visits (number L H) b) :=
  lt_of_le_of_lt (by exact_mod_cast visit_bound L H b) cap

theorem pop_transition {L W} (lay : StackLayout) (d : ℕ) (hd : d≤36) (H : SimpleGraph V)
    (π : Equiv.Perm V) (b : Branch) (w : WeightKey (2^L) → ℚ)
    (i : Fin (visits (number L H) b)) (z y : ℤ) (q : List (NativeTraversal.Slot L)) (m : Memory)
    (cap : Graph.Division.Room W (visits (number L H) b))
    (pre : Repr lay (.value (d+1) y :: .cursor d H π b w i.val z :: q) m) :
    ∃ f ≤ 5, ∃ o, Runs W (pop d (reg d (lengthField b))) m f o ∧
      Repr lay (.cursor d H π b w (i.val+1) (z+(numbered H b i).coeff*y)::q) o ∧
      Fits W (o (reg d .flag)) ∧ (o (reg d .flag)<0 ↔ i.val+1<visits (number L H) b) := by
  obtain ⟨global,child,_,⟨wt,prepared,len,ix,val⟩,⟨hi,coeff⟩,anc⟩ := pre
  obtain ⟨o,run,os,oi,flag,fr⟩ := pop_runs W d (lengthField b)
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) m
  have plane (a : ℕ) (ha:297≤a) := fr (a:ℤ) (distinctData ha hd _) (distinctData ha hd _) (distinctData ha hd _)
  have parent (j) (hj:j<d) (k) := fr (reg j k) (ne_of_lt (separate hj _ _))
    (ne_of_lt (separate hj _ _)) (ne_of_lt (separate hj _ _))
  have lengths (k : Branch) : o (reg d (lengthField k)) = m (reg d (lengthField k)) :=
    fr _ (different d (by cases k <;> decide)) (different d (by cases k <;> decide))
        (different d (by cases k <;> decide))
  have zp : o 0=m 0 := fr _ (ne_of_lt (reg_positive ..)) (ne_of_lt (reg_positive ..)) (ne_of_lt (reg_positive ..))
  have ptr : o (reg d .weights)=m (reg d .weights) :=
    fr _ (different d (by decide)) (different d (by decide)) (different d (by decide))
  change m (reg (d+1) .value) = y at child
  change m (reg d .index) = (i.val:ℤ) at ix
  change m (reg d .value) = z at val
  change m (reg d .coefficient) = (numbered H b i).coeff at coeff
  rw [val,coeff,child] at os
  rw [ix] at oi
  rw [ix,len] at flag
  have ilt := i.isLt
  refine ⟨5,le_rfl,o,run,⟨global.transfer zp (plane 320 (by decide)) (plane 321 (by decide)),⟨weights_transfer wt ptr plane,lay.transferAll _ _ _ _ plane prepared,
    fun k => (lengths k).trans (len k),by exact_mod_cast oi,os⟩,saved_transfer lay d q plane parent anc⟩,?_,?_⟩
  · rw [flag]; apply cap.fits <;> omega
  · rw [flag]; omega

end VWZClique.IntegerRAM.NativeFrame
end

/- NativeFrameAssembly -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

/-- A fixed selection of the proved sparse commands, shared by all input sizes. -/
noncomputable def leafOp : ℕ → SimpleGraph V → Command := Classical.choose leaf_transitions

def ops (leaf : ℕ → SimpleGraph V → Command)
    (project : ℕ → SimpleGraph V → Equiv.Perm V → Command)
    (push : ℕ → SimpleGraph V → Equiv.Perm V → Branch → Command) : Operations where
  leaf := leaf
  project := project
  push := push
  reset d _ := reset d
  pop d _ b := pop d (reg d (lengthField b))
  test d := reg d .flag
  finish _ := finish

theorem compile_from_two {L W : ℕ} {lay : StackLayout} {proj push P B}
    (k : @Kernels L W lay proj push P B)
    (mem : ∀ d ≤ 36, Graph.Division.Room W (lay.base d + 9*(2^L)+81*(2^L*2^L)))
    (six : Graph.Division.Room W ((2^L)^6)) :
    Correct (ops leafOp proj push) W (@Repr L lay) (fees L P B) := by
  constructor
  · intro d H hh w q hd hw
    exact (Classical.choose_spec (Classical.choose_spec leaf_transitions))
      L W d (by omega) lay H hh w hw q (mem d (by omega))
  · exact k.projected
  · intro d H π b e w i z q hd
    exact reset_transition lay d hd H π b e w i z q
  · intro d H π b w i z q _
    exact finish_transition lay d H π b w i z q
  · exact k.child
  · intro d H π b i w z y q m hd prepared
    exact pop_transition lay d hd.le H π b w i z y q m (visit_room H b six) prepared

/-- The physical table/stack program has no remaining scheduling, recursive
loop, leaf, or header-control hypotheses. -/
theorem execute_from_two {L W : ℕ} {lay : StackLayout} {proj push P B}
    (k : @Kernels L W lay proj push P B)
    (mem : ∀ d ≤ 36, Graph.Division.Room W (lay.base d + 9*(2^L)+81*(2^L*2^L)))
    (six : Graph.Division.Room W ((2^L)^6)) {H : SimpleGraph V} (p : Plan H) (d : ℕ)
    (hd : d+Nat.card H.edgeSet≤36) (w : WeightKey (2^L) → ℚ) (hw : ∀ i, Binary (w i)) (q : List (NativeTraversal.Slot L)) :
    Transition W (Repr lay) (emitPlan (ops leafOp proj push) p d) (.input d w::q)
      (.value d (integerPlan L p w)::q) (cost L (fees L P B) p) :=
  compiled_correct _ _ _ (compile_from_two k mem six) p d hd w hw q

end VWZClique.IntegerRAM.NativeFrame
end

/- NativeFoldTime -/
section
namespace VWZClique.NativeTraversal
open UniformFolds
open OAI.MatrixMultiplication.Arithmetic

/-- Every recursive call reserves an n^5 term, even at an internal node.
This pays for materializing that child's tables, with any polynomial in log(n)
overhead carried by a common multiplier. -/
theorem work_floor (mm : ℕ → ℕ) (T U G L : ℕ) {H : SimpleGraph V} (p : Plan H) :
    U*(2^L)^5 ≤ planWork mm T U G L p := by
  cases p with
  | leaf => exact le_rfl
  | split H π h kids => simp only [planWork,splitWork]; omega

theorem cost_le (mm : ℕ → ℕ) (T U G L A : ℕ) (c : Charges)
    (hl : ∀ H, c.small H ≤ A*(U*(2^L)^5))
    (hp : ∀ H, c.projection H + 2*c.reset+c.finish ≤ A*(projected mm T U L H+3))
    (hs : ∀ H, c.push H + c.pop + 1 ≤ A*(U*(2^L)^5))
    {H : SimpleGraph V} (p : Plan H) :
    cost L c p ≤ (Nat.card H.edgeSet+1)*A*planWork mm T U G L p := by
  induction p with
  | leaf H hh =>
    apply (hl H).trans
    change A*(U*(2^L)^5) ≤ (Nat.card H.edgeSet+1)*A*(U*(2^L)^5)
    gcongr
    exact Nat.le_mul_of_pos_left _ (by omega)
  | split H π hh kids ih =>
    let e := Nat.card H.edgeSet
    let B := (e+1)*A
    let m := number L H
    let w (d : Branch) := planWork mm T U G L (kids d)
    have hA : A ≤ B := Nat.le_mul_of_pos_left _ (by omega)
    have hchild (d : Branch) : c.push H + (cost L c (kids d) + c.pop) + 1 ≤
        B*(G*(2^L)^2+w d+3) := by
      have de := branch_smaller H π hh d
      have lo := work_floor mm T U G L (kids d)
      let e' := Nat.card (child (WeightedProof.slots π H) d).edgeSet
      have small : e'+1 ≤ e := by exact de
      have h := ih d
      change cost L c (kids d) ≤ (e'+1)*A*w d at h
      calc
        _ = (c.push H+c.pop+1)+cost L c (kids d) := by omega
        _ ≤ A*w d + (e'+1)*A*w d := Nat.add_le_add ((hs H).trans (Nat.mul_le_mul_left _ lo)) h
        _ ≤ A*w d + e*A*w d := by gcongr
        _ = B*w d := by dsimp [B]; ring
        _ ≤ _ := by gcongr <;> omega
    have head := (hp H).trans (Nat.mul_le_mul_right _ hA)
    let pr := projected mm T U L H
    change c.projection H + (m*(c.push H+(cost L c (kids .left)+c.pop)+1) +
      (c.reset+(m*(c.push H+(cost L c (kids .right)+c.pop)+1)+
      (c.reset+((m*m)*(c.push H+(cost L c (kids .both)+c.pop)+1)+c.finish))))) ≤
      B*(pr + m*(G*(2^L)^2+w .left+3) + m*(G*(2^L)^2+w .right+3) +
        m^2*(G*(2^L)^2+w .both+3)+3)
    have comb := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add head
      (Nat.mul_le_mul_left m (hchild .left))) (Nat.mul_le_mul_left m (hchild .right)))
      (Nat.mul_le_mul_left (m*m) (hchild .both))
    change c.projection H+2*c.reset+c.finish + _ + _ + _ ≤ B*(pr+3)+_+_+_ at comb
    ring_nf at comb ⊢
    exact comb

end VWZClique.NativeTraversal
end

/- WordButterfly -/
section
/-! A fixed native signed-word program for one product-basis digit.
    Four contiguous input stripes are streamed into one contiguous output array.
    Each output quartet has the order 00, 11, 01+10, 01−10. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

namespace Reg
end Reg

def effect (m : Memory) : Atom → Memory
  | .one d => update m d 1
  | .add d a b => update m d (m a + m b)
  | .sub d a b => update m d (m a - m b)
  | .mul d a b => update m d (m a * m b)
  | .load d p => update m d (m (m p))
  | .store p s => update m (m p) (m s)

def safe (W : ℕ) (m : Memory) : Atom → Prop
  | .load _ p | .store p _ => Fits W (m p)
  | _ => True

def safeLine (W : ℕ) (m : Memory) : List Atom → Prop
  | [] => True
  | a :: as => safe W m a ∧ safeLine W (effect m a) as

theorem line_runs {W : ℕ} (as : List Atom) (m : Memory) (h : safeLine W m as) :
    Runs W (line as) m as.length (as.foldl effect m) := by
  induction as generalizing m with
  | nil => exact .skip _
  | cons a as ih =>
    have ha : Step W a m (effect m a) := by
      have hh := h.1
      cases a with
      | one => exact .one ..
      | add => exact .add ..
      | sub => exact .sub ..
      | mul => exact .mul ..
      | load => exact .load _ _ _ hh
      | store => exact .store _ _ _ hh
    rw [List.length_cons,Nat.add_comm]
    exact .seq (.atom ha) (ih _ h.2)

set_option maxHeartbeats 1600000

attribute [local simp] Reg.p0 Reg.p1 Reg.p2 Reg.p3 Reg.dest Reg.x0 Reg.x1 Reg.x2 Reg.x3
  Reg.sum Reg.diff Reg.count Reg.srcBase Reg.dstBase Reg.stride Reg.one Reg.zero Reg.stages Reg.swap

end VWZClique.IntegerRAM.Butterfly
end

/- NativeDyadicSize -/
section
namespace VWZClique.IntegerRAM.Dyadic
open Structured Butterfly

abbrev Nreg : ℤ := -1
abbrev Qreg : ℤ := -3
abbrev Lreg : ℤ := -12
abbrev Ureg : ℤ := -13
abbrev Freg : ℤ := -14

def powCode : ℕ → List Atom
  | 0 => [.one Nreg]
  | t+1 => powCode t ++ [.mul Nreg Nreg 0]

def setupOps : List Atom :=
  [.one Qreg,.sub Lreg Lreg Lreg,.one Ureg,.sub Freg Nreg Qreg,.sub Freg Freg Ureg]

def doubleOps : List Atom := [.add Qreg Qreg Qreg,.add Lreg Lreg Ureg,.sub Freg Qreg Nreg]
def grow : Command := .repeatWhileNegative (line doubleOps) Freg
def sizeProgram (t : ℕ) := Command.seq (line (powCode t)) <|
  .seq (line setupOps) (.whenNonnegative Freg grow)

private theorem lineAppend (a b : List Atom) (m : Memory) :
    (a++b).foldl effect m = b.foldl effect (a.foldl effect m) := List.foldl_append

private theorem pow_spec (t : ℕ) (m : Memory) :
    ∀ W : ℕ, safeLine W m (powCode t) ∧
      (powCode t).foldl effect m = update m Nreg (m 0 ^ t) ∧ (powCode t).length=t+1 := by
  induction t with
  | zero => intro W; simp [powCode,safeLine,safe,effect]
  | succ t ih =>
    intro W
    obtain ⟨s,e,l⟩ := ih W
    have app (as bs : List Atom) (a : Memory) : safeLine W a (as++bs) ↔
        safeLine W a as ∧ safeLine W (as.foldl effect a) bs := by
      induction as generalizing a with
      | nil => simp [safeLine]
      | cons x xs ih => simp [safeLine,ih,and_assoc]
    refine ⟨by simp [powCode,app,s,safeLine,safe],?_,by simp [powCode,l]⟩
    rw [powCode,lineAppend,e]
    funext z
    by_cases hz : z=Nreg <;> simp [effect,update,hz,Nreg,pow_succ] at *

def frame (m o : Memory) := ∀ z : ℕ, o z=m z

private theorem grow_runs {N W : ℕ} (room : Graph.Division.Room W (2*N))
    {j r : ℕ} (len : j+r=Nat.clog 2 N) (hr : 0<r) (m : Memory)
    (hN : m Nreg=N) (hQ : m Qreg=((2:ℕ)^j:ℕ)) (hL : m Lreg=j) (hU : m Ureg=1) :
    ∃ o, Runs W grow m (4*r) o ∧ frame m o ∧ o Nreg=N ∧
      o Qreg=((2:ℕ)^(Nat.clog 2 N):ℕ) ∧ o Lreg=Nat.clog 2 N := by
  induction r generalizing j m with
  | zero => omega
  | succ r ih =>
    let a := doubleOps.foldl effect m
    have act : Runs W (line doubleOps) m 3 a := line_runs _ _ (by simp [doubleOps,safeLine,safe])
    have q : a Qreg=((2:ℕ)^(j+1):ℕ) := by simp [a,doubleOps,effect,update,hQ,pow_succ]; ring
    have n : a Nreg=N := by simp [a,doubleOps,effect,update,hN]
    have l : a Lreg=((j+1:ℕ):ℤ) := by simp [a,doubleOps,effect,update,hL,hU]
    have one : a Ureg=1 := by simp [a,doubleOps,effect,update,hU]
    have f : a Freg=(((2:ℕ)^(j+1):ℕ):ℤ)-N := by simp [a,doubleOps,effect,update,hQ,hN,pow_succ]; ring
    have fr : frame m a := by intro z; simp [a,doubleOps,effect,update,Freg,Lreg,Qreg]
    have prev : 2^j<N := Nat.pow_lt_of_lt_clog (by omega : j<Nat.clog 2 N)
    have ub : 2^(j+1) ≤ 2*N := by rw [pow_succ]; omega
    have fit : Fits W (a Freg) := by
      rw [f]
      let t₁ : ℕ := 2^(j+1)
      change Fits W ((t₁:ℤ)-N)
      have tpos : 0≤(t₁:ℤ) := Nat.cast_nonneg _
      have tcap : (t₁:ℤ) ≤ 2*(N:ℤ) := by exact_mod_cast ub
      have nn : 0≤(N:ℤ) := Nat.cast_nonneg _
      apply room.fits <;> push_cast <;> linarith only [tpos,tcap,nn]
    by_cases fin : r=0
    · subst r
      have done : j+1=Nat.clog 2 N := by omega
      have lb : N ≤ 2^(j+1) := done ▸ Nat.le_pow_clog (by decide) N
      exact ⟨a,by simpa only [grow] using Runs.loop_done act fit (by rw [f]; omega),fr,n,done ▸ q,done ▸ l⟩
    · obtain ⟨o,run,keep,n',q',l'⟩ := ih (j:=j+1) (by omega) (by omega) a n q l one
      have lt := Nat.pow_lt_of_lt_clog (b:=2) (x:=N) (show j+1<Nat.clog 2 N by omega)
      exact ⟨o,by rw [show 4*(r+1)=3+1+4*r by omega]; exact Runs.loop_again act fit (by rw [f]; omega) run,
        fun z => (keep z).trans (fr z),n',q',l'⟩

theorem size_runs (W n t : ℕ) (hn : 1≤n) (m : Memory) (order : m 0=n)
    (room : Graph.Division.Room W (2*n^t)) :
    ∃ out, Runs W (sizeProgram t) m (t+7+4*(Nat.clog 2 (n^t))) out ∧ frame m out ∧
      out Nreg=((n^t:ℕ):ℤ) ∧ out Qreg=((2^(Nat.clog 2 (n^t)):ℕ):ℤ) ∧ out Lreg=Nat.clog 2 (n^t) := by
  let N := n^t
  let L := Nat.clog 2 N
  obtain ⟨safe,work,len⟩ := pow_spec t m W
  let s := (powCode t).foldl effect m
  have sem : s=update m Nreg (N:ℤ) := by simpa [s,N,order] using work
  have start : Runs W (line (powCode t)) m (t+1) s := len ▸ line_runs _ _ safe
  let a := setupOps.foldl effect s
  have act : Runs W (line setupOps) s 5 a := line_runs _ _ (by simp [setupOps,safeLine,Butterfly.safe])
  have n' : a Nreg=N := by simp [a,sem,setupOps,effect,update]
  have q : a Qreg=1 := by simp [a,setupOps,effect,update]
  have l : a Lreg=0 := by simp [a,setupOps,effect,update]
  have u : a Ureg=1 := by simp [a,setupOps,effect,update]
  have fl : a Freg=(N:ℤ)-2 := by simp [a,sem,setupOps,effect,update]; ring
  have pos : 1≤N := Nat.one_le_pow _ _ hn
  have fit : Fits W (a Freg) := by rw [fl]; have rr : Graph.Division.Room W (2*N) := room; apply rr.fits <;> omega
  have fr : frame m a := by intro z; simp [a,sem,setupOps,effect,update,Nreg,Qreg,Lreg,Freg,Ureg]
  by_cases zero : L=0
  · have hn' : N≤2^0 := zero ▸ Nat.le_pow_clog (by decide) N
    have neg : a Freg<0 := by rw [fl]; simp at hn'; omega
    have run := start.seq (act.seq (Runs.guard_skip (c:=grow) fit neg))
    refine ⟨a,?_,fr,n',?_,?_⟩
    · change Runs W _ _ (t+7+4*L) _
      simpa [sizeProgram,zero,Nat.add_assoc] using run
    · change a Qreg=((2^L:ℕ):ℤ); simpa [zero] using q
    · change a Lreg=(L:ℤ); simpa [zero] using l
  · have gt : 1<N := by simpa using (Nat.pow_lt_of_lt_clog (b:=2) (x:=N) (by change 0<L; omega))
    obtain ⟨o,run,keep,no,qo,lo⟩ := grow_runs (N:=N) room (j:=0) (r:=L) (by simp [L]) (by omega) a n' (by simpa using q) l u
    have whole := start.seq (act.seq (Runs.guard_take fit (by rw [fl]; omega) run))
    exact ⟨o,by change Runs W _ _ (t+7+4*L) _; rw [show t+7+4*L=(t+1)+(5+(1+4*L)) by omega]; exact whole,fun z => (keep z).trans (fr z),no,qo,lo⟩

end VWZClique.IntegerRAM.Dyadic
end

/- NativeSquareExpr -/
section
namespace VWZClique.IntegerRAM.SquareCode
open Structured

def Expr.val (m : Memory) : Expr → ℤ
  | .zero => 0
  | .one => 1
  | .reg r => m r
  | .read a => m (a.val m)
  | .add a b => a.val m + b.val m
  | .sub a b => a.val m - b.val m
  | .mul a b => a.val m * b.val m

def Expr.safe (d : ℤ) (W : ℕ) (m : Memory) : Expr → Prop
  | .zero | .one => True
  | .reg r => d < r
  | .read a => a.safe d W m ∧ d < a.val m ∧ Fits W (a.val m)
  | .add a b | .sub a b | .mul a b => a.safe d W m ∧ b.safe d W m

theorem carry {d D : ℤ} (hd : D ≤ d) {W : ℕ} {m p : Memory}
    (agree : ∀ i, d < i → p i=m i) (x : Expr) (hx : x.safe d W m) :
    x.val p=x.val m ∧ x.safe D W p := by
  induction x with
  | zero => exact ⟨rfl,True.intro⟩
  | one => exact ⟨rfl,True.intro⟩
  | reg i => exact ⟨agree _ hx,Int.lt_of_le_of_lt hd hx⟩
  | read x ih =>
    obtain ⟨v,s⟩ := ih hx.1
    exact ⟨(congrArg p v).trans (agree _ hx.2.1),s,v ▸ Int.lt_of_le_of_lt hd hx.2.1,v ▸ hx.2.2⟩
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    obtain ⟨va,sa⟩ := ia hx.1
    obtain ⟨vb,sb⟩ := ib hx.2
    exact ⟨by simp only [Expr.val,va,vb],sa,sb⟩

def Result (W : ℕ) (m : Memory) (d : ℤ) (x : Expr) : Prop :=
  ∃ out : Memory, Runs W (x.code d) m x.steps out ∧ out d=x.val m ∧ ∀ i, d < i → out i=m i

private theorem joinOp {W : ℕ} {m : Memory} {d : ℤ} (a b x : Expr) (op : Atom) (f : ℤ → ℤ → ℤ)
    (hc : x.code d=binary (a.code d) (b.code (d-1)) op) (ht : x.steps=a.steps+(b.steps+1))
    (hv : x.val m=f (a.val m) (b.val m))
    (action : ∀ p : Memory, Step W op p (update p d (f (p d) (p (d-1)))))
    (ha : Result W m d a) (hb : b.safe d W m)
    (rhs : ∀ p d', b.safe d' W p → Result W p d' b) : Result W m d x := by
  obtain ⟨u,hu,ua,uf⟩ := ha
  obtain ⟨v₀,b₀⟩ := carry (show d-1 ≤ d by omega) uf b hb
  obtain ⟨v,hv',vb,vf⟩ := rhs u _ b₀
  refine ⟨update v d (f (v d) (v (d-1))),?_,?_,?_⟩
  · rw [hc,ht]; exact Runs.seq hu (Runs.seq hv' (Runs.atom (action v)))
  · simp [update,vf d (by omega),ua,vb,v₀,hv]
  · intro i hi
    rw [update,if_neg (by omega),vf _ (by omega),uf _ hi]

theorem Expr.run (x : Expr) {W : ℕ} (m : Memory) (d : ℤ) (hx : x.safe d W m) :
    Result W m d x := by
  induction x generalizing m d with
  | one =>
    exact ⟨_,.atom (.one _ _),by simp [update,val],fun i hi => if_neg (by omega)⟩
  | zero =>
    exact ⟨_,.atom (.sub _ _ _ _),by simp [update,Expr.val],fun i hi => if_neg (by omega)⟩
  | reg i =>
    let p := update m d (m d-m d)
    refine ⟨_,Runs.seq (.atom (.sub _ _ _ _)) (.atom (.add p d d i)),?_,?_⟩
    · have diff : i≠d := by change d < i at hx; omega
      simp [p,update,Expr.val,diff]
    · intro j hj
      simp only [p,update,if_neg (by omega : j≠d)]
  | read a ih =>
    obtain ⟨p,hp,pv,pf⟩ := ih m d hx.1
    have fit : Fits W (p d) := pv ▸ hx.2.2
    refine ⟨_,Runs.seq hp (.atom (.load p d d fit)),?_,?_⟩
    · simp [update,pv,pf _ hx.2.1,Expr.val]
    · intro i hi
      simp only [update,if_neg ((by omega : i≠d)),pf _ hi]
  | add a b ia ib => exact joinOp a b _ _ (·+·) rfl rfl rfl (fun p => .add p _ _ _) (ia _ _ hx.1) hx.2 ib
  | sub a b ia ib => exact joinOp a b _ _ (·-·) rfl rfl rfl (fun p => .sub p _ _ _) (ia _ _ hx.1) hx.2 ib
  | mul a b ia ib => exact joinOp a b _ _ (·*·) rfl rfl rfl (fun p => .mul p _ _ _) (ia _ _ hx.1) hx.2 ib

@[simp] theorem Expr.num_val (m : Memory) (n : ℕ) : (num n).val m=n := by
  induction n <;> simp_all [num,val]

@[simp] theorem Expr.num_safe (m : Memory) (d : ℤ) (W n : ℕ) : (num n).safe d W m := by
  induction n <;> simp_all [num,safe]

end VWZClique.IntegerRAM.SquareCode
end

/- NativeDyadicCell -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph SquareCode Structured

/-- Negative registers used by the copy pass: source size, new size, row and column. -/
def n := Expr.reg (-1)
def q := Expr.reg (-3)
def x := Expr.reg (-4)
def y := Expr.reg (-5)
def src := Expr.add .one (.mul (.reg (-2)) (.reg (-2)))
def words (d : Expr) := Expr.add (.mul (.num 9) d) (.mul (.num 81) (.mul d d))
def dst := Expr.add src (words n)

def index (s : Shape) (d : Expr) : Expr := match s with
  | .unary i => .add (.mul (.num i.val) d) x
  | .cross i j => .add (.mul (.num 9) d) (.add
      (.mul (.num (i.val*9+j.val)) (.mul d d)) (.add (.mul x d) y))

def offset (s : Shape) (D a b : ℕ) : ℕ := match s with
  | .unary i => i.val*D+a
  | .cross i j => 9*D+(i.val*9+j.val)*(D*D)+a*D+b

theorem index_val (s : Shape) (d : Expr) {m : Memory} {a b D : ℕ}
    (hD : d.val m=D) (ha : m (-4)=a) (hb : m (-5)=b) :
    (index s d).val m=(offset s D a b:ℤ) := by
  cases s <;> simp [index,offset,Expr.val,x,y,ha,hb,hD] <;> ring

theorem index_safe (s : Shape) (d : Expr) {W : ℕ} (m : Memory) (f : ℤ) (hf : f < -5)
    (hd : d.safe f W m) : (index s d).safe f W m := by
  cases s <;> simp [index,Expr.safe,x,y,hd] <;> omega

def stay := Expr.sub (.sub n x) .one
def stayCol (s : Shape) := match s with
  | .unary _ => Expr.zero
  | .cross _ _ => Expr.sub (.sub n y) .one

/-- A single range check followed by a conditional output load. The two tests use
separate scratch registers, and the default result is zero. -/
def readCode (s : Shape) : Command :=
  .seq (stay.code (-200)) (.seq ((stayCol s).code (-201))
    (.seq (.atom (.sub (-230) (-230) (-230))) (.whenNonnegative (-200)
      (.whenNonnegative (-201) ((Expr.read (.add src (index s n))).code (-230))))))

def unary : Shape → Bool
  | .unary _ => true
  | .cross _ _ => false

def colOK (s : Shape) (N v : ℕ) : Prop := match s with
  | .unary _ => True
  | .cross _ _ => v<N

instance (s : Shape) (N v : ℕ) : Decidable (colOK s N v) := by cases s <;> dsimp [colOK] <;> infer_instance

def value (m : Memory) (s : Shape) (base N u v : ℕ) : ℤ :=
  if u<N ∧ colOK s N v then m ((base+offset s N u v:ℕ):ℤ) else 0

def readBudget (s : Shape) := stay.steps+(stayCol s).steps+3+
  (Expr.read (.add src (index s n))).steps

theorem read_run {W N D n₀ u v : ℕ} (s : Shape) (m : Memory)
    (hN : m (-1)=N) (hn : m (-2)=n₀) (hu : m (-4)=u) (hv : m (-5)=v)
    (uD : u<D) (vD : v<D) (cap : Division.Room W (N+D+1))
    (space : u<N → colOK s N v → Fits W ((1+n₀*n₀+offset s N u v:ℕ):ℤ)) :
    ∃ t≤readBudget s, ∃ out, Runs W (readCode s) m t out ∧
      out (-230)=value m s (1+n₀*n₀) N u v ∧ ∀ j : ℤ, -200<j → out j=m j := by
  have sf : stay.safe (-200) W m := by simp [stay,Expr.safe,n,x]
  obtain ⟨a,runA,fa,keepA⟩ := stay.run m _ sf
  have af : a (-200)=(N:ℤ)-u-1 := by simpa [stay,n,x,Expr.val,hN,hu] using fa
  have cf : (stayCol s).safe (-201) W a := by cases s <;> simp [stayCol,Expr.safe,n,y]
  obtain ⟨b,runB,fb,keepB⟩ := (stayCol s).run a _ cf
  let c := update b (-230) (b (-230)-b (-230))
  have clear : Runs W (.atom (.sub (-230) (-230) (-230))) b 1 c := .atom (.sub ..)
  have outside (j : ℤ) (hj : -200<j) : c j=m j := by
    simp only [c,update,if_neg (by omega : j≠ -230),keepB j (by omega),keepA j hj]
  have ax : c (-200)=(N:ℤ)-u-1 := by change update b (-230) _ (-200) = _; rw [update,if_neg (by decide),keepB _ (by decide),af]
  have byval : c (-201)=(if unary s then 0 else (N:ℤ)-v-1) := by
    cases s <;> simp [unary,c,update,fb,stayCol,n,y,Expr.val,keepA _ (by decide : (-200:ℤ)< -1),
      keepA _ (by decide : (-200:ℤ)< -5),hN,hv]
  have fitX : Fits W (c (-200)) := by rw [ax]; apply cap.fits <;> push_cast <;> omega
  have fitY : Fits W (c (-201)) := by rw [byval]; split <;> apply cap.fits <;> push_cast <;> omega
  have ytest : ¬ c (-201)<0 ↔ colOK s N v := by
    rw [byval]; cases s <;> simp [colOK,unary] <;> omega
  let e := Expr.read (.add src (index s n))
  have srcval : src.val c=((1+n₀*n₀:ℕ):ℤ) := by simp [src,Expr.val,outside _ (by decide : (-200:ℤ)< -2),hn]
  have off : (index s n).val c=(offset s N u v:ℤ) :=
    index_val _ _ ((outside _ (by decide)).trans hN) ((outside _ (by decide)).trans hu) ((outside _ (by decide)).trans hv)
  by_cases xok : u<N
  · have passX : ¬c (-200)<0 := by omega
    by_cases yok : colOK s N v
    · have es : e.safe (-230) W c := by
        refine ⟨⟨by simp [src,Expr.safe],index_safe s _ c _ (by decide) (by simp [n,Expr.safe])⟩,?_,?_⟩
        all_goals simp only [Expr.val,srcval,off,←Int.natCast_add]
        · exact lt_of_lt_of_le (by decide : (-230:ℤ)<0) (Int.natCast_nonneg _)
        · exact space xok yok
      obtain ⟨o,load,found,fr⟩ := e.run c (-230) es
      refine ⟨_,?_,o,.seq runA (.seq runB (.seq clear (.guard_take fitX passX (.guard_take fitY (ytest.mpr yok) load)))),?_,?_⟩
      · unfold readBudget; dsimp [e]; omega
      · have carry := outside ((1+n₀*n₀+offset s N u v:ℕ):ℤ) (lt_of_lt_of_le (by decide : (-200:ℤ)<0) (Int.natCast_nonneg _))
        simp only [value,if_pos (And.intro xok yok)]
        exact found.trans (by simpa only [e,Expr.val,srcval,off,←Int.natCast_add] using carry)
      · exact fun j hj => (fr j (by omega)).trans (outside j hj)
    · refine ⟨_,?_,c,.seq runA (.seq runB (.seq clear (.guard_take fitX passX (.guard_skip fitY (by by_contra h; exact yok (ytest.mp h)))))),?_,outside⟩
      · unfold readBudget; omega
      · simp [c,update,value,yok]
  · refine ⟨_,?_,c,.seq runA (.seq runB (.seq clear (.guard_skip fitX (by omega)))),?_,outside⟩
    · unfold readBudget; omega
    · simp [c,update,value,xok]

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicWrite -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured SquareCode

def address (s : Shape) (n₀ N Q u v : ℕ) := target n₀ N+offset s Q u v

theorem offset_lt (s : Shape) {N x y : ℕ} (hx : x<N) (hy : y<N) : offset s N x y < space N := by
  cases s with
  | unary i =>
    have hi : i.val+1≤9 := i.isLt
    have h := Nat.mul_le_mul_right N hi
    simp [offset,space] at *; nlinarith
  | cross i j =>
    have hi : i.val < 9 := i.isLt
    have hj : j.val < 9 := j.isLt
    have h := Nat.mul_le_mul_right (N*N) (by omega : i.val*9+j.val+1 ≤81)
    have h' := Nat.mul_le_mul_right N hx
    rw [Nat.succ_mul] at h'
    simp only [Nat.add_mul,one_mul] at h
    change 9*N+(i.val*9+j.val)*(N*N)+x*N+y<9*N+81*(N*N)
    nlinarith only [h,h',hy]

def writer (s : Shape) : Command :=
  .seq ((.add dst (index s q) : Expr).code (-188))
  (.seq (readCode s) (.atom (.store (-188) (-230))))

def writeBudget (s : Shape) := (Expr.add dst (index s q)).steps+readBudget s+1

theorem write_run {W N D n₀ u v : ℕ} (s : Shape) (m : Memory)
    (hN : m (-1)=N) (hD : m (-3)=D) (hn : m (-2)=n₀) (hu : m (-4)=u) (hv : m (-5)=v)
    (uD : u<D) (vD : v<D) (hND : N≤D)
    (room : Division.Room W (target n₀ N+space D+N+D+1)) :
    ∃ t≤writeBudget s, ∃ out, Runs W (writer s) m t out ∧
      ∀ j : ℤ, -188<j → out j =
        if j=(address s n₀ N D u v:ℤ) then value m s (origin n₀) N u v else m j := by
  let a := Expr.add dst (index s q)
  have safe : a.safe (-188) W m := by
    refine ⟨?_,index_safe s _ m _ (by decide) (by simp [q,Expr.safe])⟩
    simp [dst,src,words,n,Expr.safe]
  have val : a.val m=(address s n₀ N D u v:ℤ) := by
    have hi := index_val s q (show q.val m=D from hD) hu hv
    simp only [a,Expr.val,hi,dst,src,words,n,Expr.num_val,hN,hn,space,origin,target,address]
    push_cast; ring
  obtain ⟨p,addr,pa,pf⟩ := a.run m (-188) safe
  have r : Division.Room W (N+D+1) := lt_of_le_of_lt (Nat.cast_le.mpr (by omega)) room
  have hh : ∀ s' : Shape, ∀ a' b' : ℕ, a'<N → colOK s' N b' →
    Fits W ((origin n₀+offset s' N a' b':ℕ):ℤ) := by
    intro j a' b' ha ok
    have small : offset j N a' b' < space N := by
      cases j with
      | unary i => exact offset_lt (.unary i) (y:=0) ha (by omega)
      | cross i j => exact offset_lt (.cross i j) ha ok
    apply room.fits <;> unfold target <;> push_cast <;> omega
  obtain ⟨t,bt,v',read,pv,fr⟩ := read_run s p ((pf _ (by decide)).trans hN)
    ((pf _ (by decide)).trans hn) ((pf _ (by decide)).trans hu) ((pf _ (by decide)).trans hv)
    uD vD r (hh s u v)
  have a' := (fr _ (by decide : (-200:ℤ) < -188)).trans (pa.trans val)
  have bound := offset_lt s uD vD
  have fits : Fits W (v' (-188)) := by
    rw [a']; apply room.fits <;> unfold address <;> push_cast <;> omega
  have vv : value p s (origin n₀) N u v=value m s (origin n₀) N u v := by
    unfold value; split
    · apply pf; have := Int.natCast_nonneg (origin n₀+offset s N u v); omega
    · rfl
  refine ⟨_,?_,_,addr.seq (read.seq (.atom (.store v' (-188) (-230) fits))),?_⟩
  · dsimp [writeBudget,a] at *; omega
  · intro j hj
    have v'':=vv
    unfold origin at v''
    rw [update,a',pv,v'',fr j (by omega),pf j hj]
    rfl

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeSquareGrid -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

abbrev Heap := ℕ → ℤ
def heap (m : IntegerRAM.Memory) : Heap := fun a => m a
def regs (i : ℤ) (m p : IntegerRAM.Memory) := ∀ z, (i < z ∨ floor < z ∧ z <  -8) → z < 0 → p z=m z

def foldRange (f : ℕ → Heap → Heap) : ℕ → Heap → Heap
  | 0,H => H
  | q+1,H => f q (foldRange f q H)

/-- A counted native loop, with persistent data modeled by a pure update to
nonnegative cells. The outer loop counters are preserved. -/
theorem loop_run {W N B : ℕ} {i lim : ℤ} (hi : -6 ≤ i) (hi' : i ≤ -4)
    (hl : i < lim) (hl' : lim < 0) (hn : 0 < N) (m : IntegerRAM.Memory) (bound : m lim=N)
    (guardFit : ∀ q : ℕ, q ≤ N → Fits W ((q:ℤ)-N))
    (body : Command) (f : ℕ → Heap → Heap)
    (step : ∀ q < N, ∀ x : IntegerRAM.Memory, regs i m x → x i=q → x (-7)=1 →
      ∃ t, t ≤ B ∧ ∃ out, Runs W body x t out ∧ heap out=f q (heap x) ∧ regs (i-1) x out ∧ out (-7)=1) :
    ∃ t, t ≤ 2+N*(B+3) ∧ ∃ out, Runs W (loop i lim body) m t out ∧ heap out=foldRange f N (heap m) ∧
      regs i m out ∧ out (-7)=1 := by
  let I (q : ℕ) (x : IntegerRAM.Memory) := x i=q ∧ x (-7)=1 ∧ regs i m x ∧ heap x=foldRange f q (heap m)
  let s := update m (-7) 1
  let init := update s i (s i-s i)
  have ini : I 0 init := by
    refine ⟨by simp [init,update],by simp [init,s,update,if_neg (by omega : (-7:ℤ)≠i)],?_,?_⟩
    · intro z h₁ h₂
      unfold floor at h₁
      simp only [init,s,update,if_neg (by omega : z≠i),if_neg (by omega : z≠ -7)]
    · funext z
      change init z = m z
      simp only [init,s,update,if_neg (by omega : (z:ℤ)≠i),if_neg (by omega : (z:ℤ)≠ -7)]
  have advance (q : ℕ) (hq : q < N) (x : IntegerRAM.Memory) (inv : I q x) :
      ∃ t, t ≤ B ∧ ∃ o, Runs W body x t o ∧ o i=q ∧ o (-7)=1 ∧ o lim=N ∧
        I (q+1) (nextMemory o i (-8) q N) := by
    obtain ⟨idx,one,ctx,data⟩ := inv
    obtain ⟨t,ht,o,run,dat,keep,unit⟩ := step q hq x ctx idx one
    have oi := (keep i (by omega) (by omega)).trans idx
    have ol := (keep lim (by omega) hl').trans ((ctx lim (Or.inl hl) hl').trans bound)
    refine ⟨t,ht,o,run,oi,unit,ol,?_,?_,?_,?_⟩
    · simp [nextMemory,update,if_neg (by omega : i≠ -8)]
    · simp [nextMemory,update,if_neg (by omega : (-7:ℤ)≠i),unit]
    · intro z hz hz'
      unfold floor at hz
      simp only [nextMemory,update,if_neg (by omega : z≠ -8),if_neg (by omega : z≠i)]
      exact (keep z (by rcases hz with h|h; exact Or.inl (by omega); exact Or.inr h) hz').trans (ctx z hz hz')
    · funext z
      change (nextMemory o i (-8) q N) z = _
      simp only [nextMemory,update,if_neg (by omega : (z:ℤ)≠ -8),if_neg (by omega : (z:ℤ)≠i)]
      exact congrFun (dat.trans (congrArg (f q) data)) z
  obtain ⟨t,ht,o,run,last⟩ := repeatN_runs hn body (by omega : lim≠i) I guardFit advance ini
  exact ⟨1+(1+t),by omega,o,Runs.seq (.atom (.one m (-7))) (Runs.seq (.atom (.sub s i i i)) run),
    last.2.2.2,last.2.2.1,last.2.1⟩

def gridFold (f : ℕ → ℕ → ℕ → Heap → Heap) (N side : ℕ) (H : Heap) :=
  foldRange (fun p => foldRange (fun u => foldRange (fun v => f p u v) side) side) N H

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeSquareScatter -/
section
namespace VWZClique.IntegerRAM.SquareCode.Layout

abbrev Position := ℕ × ℕ × ℕ
def points (N D : ℕ) : List Position :=
  (List.range N).flatMap fun p => (List.range D).flatMap fun u => (List.range D).map fun v => (p,u,v)

theorem points_mem (N D : ℕ) (a : Position) :
    a ∈ points N D ↔ a.1 < N ∧ a.2.1 < D ∧ a.2.2 < D := by
  rcases a with ⟨p,u,v⟩
  simp [points] <;> grind

private theorem foldRange_list (n : ℕ) (f : ℕ → Heap → Heap) (H : Heap) :
    foldRange f n H = (List.range n).foldl (fun a i => f i a) H := by
  induction n with
  | zero => rfl
  | succ n ih => simp [foldRange,List.range_succ,ih]

theorem gridFold_list (f : ℕ → ℕ → ℕ → Heap → Heap) (N D : ℕ) (H : Heap) :
    gridFold f N D H = (points N D).foldl (fun a i => f i.1 i.2.1 i.2.2 a) H := by
  simp only [gridFold,foldRange_list,points,List.foldl_flatMap,List.foldl_map]

def scatter (dst : Position → ℕ) (value : Position → Heap → ℤ) (a : Position) (H : Heap) :
    Heap := fun z => if z=dst a then value a H else H z

end VWZClique.IntegerRAM.SquareCode.Layout
end

/- NativeDyadicGrid -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured SquareCode.Layout

def grid (s : Shape) := loop (-4) (-3) (loop (-5) (-3) (writer s))

def gridCost (s : Shape) (D : ℕ) := 2+D*((2+D*(writeBudget s+3))+3)

def datum (H : Heap) (s : Shape) (n₀ N u v : ℕ) : ℤ :=
  if u<N ∧ colOK s N v then H (origin n₀+offset s N u v) else 0

def setCell (s : Shape) (n₀ N D u v : ℕ) (H : Heap) : Heap :=
  fun z => if z=address s n₀ N D u v then datum H s n₀ N u v else H z

abbrev roomNeeded (n₀ N D : ℕ) := target n₀ N+space D+N+D+1

theorem grid_runs {W N D n₀ : ℕ} (s : Shape) (m : Memory)
    (hN : m (-1)=N) (hD : m (-3)=D) (hn : m (-2)=n₀) (hpos : 0<D) (hND : N≤D)
    (room : Division.Room W (roomNeeded n₀ N D)) :
    ∃ t≤gridCost s D, ∃ out, Runs W (grid s) m t out ∧
      heap out=foldRange (fun u => foldRange (fun v => setCell s n₀ N D u v) D) D (heap m) ∧
      regs (-4) m out ∧ out (-7)=1 := by
  have guard (v : ℕ) (hv : v≤D) : Fits W ((v:ℤ)-D) := by
    apply room.fits <;> unfold roomNeeded <;> push_cast <;> omega
  apply loop_run (by decide) (by decide) (by decide) (by decide) hpos m hD guard
  intro u hu a ma ua _
  have da := (ma (-3) (by decide) (by decide)).trans hD
  apply loop_run (by decide) (by decide) (by decide) (by decide) hpos a da guard
  intro v hv b ab vb one
  have nb := (ab (-1) (by decide) (by decide)).trans ((ma _ (by decide) (by decide)).trans hN)
  have n₀b := (ab (-2) (by decide) (by decide)).trans ((ma _ (by decide) (by decide)).trans hn)
  have db := (ab (-3) (by decide) (by decide)).trans da
  have ub := (ab (-4) (by decide) (by decide)).trans ua
  obtain ⟨t,ht,o,run,mem⟩ := write_run s b nb db n₀b ub vb hu hv hND room
  have nz := Int.natCast_nonneg (address s n₀ N D u v)
  refine ⟨t,ht,o,run,?_,?_,?_⟩
  · funext z
    unfold setCell
    change o z=_
    simpa only [Int.natCast_inj,datum,value,heap] using (mem z (by omega))
  · intro z hz neg
    unfold floor at hz
    rw [mem z (by omega),if_neg (by omega)]
  · rw [mem _ (by decide),if_neg (by omega),one]

def blocks (sh : ℕ → Shape) : ℕ → Command
  | 0 => .skip
  | j+1 => .seq (blocks sh j) (grid (sh j))

def blockCost (sh : ℕ → Shape) (D : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => blockCost sh D j + gridCost (sh j) D

theorem blocks_run {W N D n₀ : ℕ} (sh : ℕ → Shape) (m : Memory)
    (hN : m (-1)=N) (hD : m (-3)=D) (hn : m (-2)=n₀) (hpos : 0<D) (hND : N≤D)
    (room : Division.Room W (roomNeeded n₀ N D)) (j : ℕ) :
    ∃ t≤blockCost sh D j, ∃ out, Runs W (blocks sh j) m t out ∧
      heap out=gridFold (fun a u v => setCell (sh a) n₀ N D u v) j D (heap m) ∧ regs (-4) m out := by
  induction j with
  | zero => exact ⟨0,le_rfl,m,.skip _,rfl,fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨t,ht,o,run,hHeap,fr⟩ := ih
    obtain ⟨t',ht',p,run',heap',fr',_⟩ := grid_runs (sh j) o
      ((fr _ (by decide) (by decide)).trans hN) ((fr _ (by decide) (by decide)).trans hD)
      ((fr _ (by decide) (by decide)).trans hn) hpos hND room
    exact ⟨_,Nat.add_le_add ht ht',p,run.seq run',by rw [heap', hHeap]; rfl,
      fun z hz hneg => (fr' z hz hneg).trans (fr z hz hneg)⟩

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicScatter -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open SquareCode.Layout Graph

private theorem pack {M a b x y : ℕ} (hx : x<M) (hy : y<M) (h : a*M+x=b*M+y) :
    a=b ∧ x=y := by
  have le (i j r s : ℕ) (hr : r<M) (eqn : j*M+s=i*M+r) : j ≤ i := by
    by_contra! hj
    have p := Nat.mul_le_mul_right M (show i+1≤j by omega)
    rw [Nat.succ_mul] at p
    omega
  have e := Nat.le_antisymm (le b a y x hy h) (le a b x y hx h.symm)
  exact ⟨e,by simpa only [e,Nat.add_right_inj] using h⟩

private theorem unary_limit (D : ℕ) (i : Fin 9) {u : ℕ} (hu : u<D) : i.val*D+u<9*D := by
  have h := Nat.mul_le_mul_right D i.isLt
  rw [Nat.succ_mul] at h
  omega

theorem data_agree (s t : Shape) {D u v x y n₀ N : ℕ} (H : Heap)
    (hu : u<D) (hv : v<D) (hx : x<D) (hy : y<D)
    (eqn : offset s D u v=offset t D x y) :
    datum H s n₀ N u v=datum H t n₀ N x y := by
  cases s with
  | unary i =>
    cases t with
    | unary j =>
      obtain ⟨ij,ux⟩ := pack hu hx eqn
      have e : i=j := Fin.ext ij
      subst j; subst x
      rfl
    | cross i' j' =>
      have h := unary_limit D i hu
      simp only [offset] at eqn
      omega
  | cross i j =>
    cases t with
    | unary i' =>
      have h := unary_limit D i' hx
      simp only [offset] at eqn
      omega
    | cross i' j' =>
      have red : ((i.val*9+j.val)*D+u)*D+v=((i'.val*9+j'.val)*D+x)*D+y := by
        simp only [offset] at eqn
        simp only [Nat.add_mul,Nat.mul_assoc] at eqn ⊢; omega
      obtain ⟨pref,vy⟩ := pack hv hy red
      obtain ⟨ind,ux⟩ := pack hu hx pref
      obtain ⟨ii,jj⟩ := pack j.isLt j'.isLt ind
      have e₁ : i=i' := Fin.ext ii
      have e₂ : j=j' := Fin.ext jj
      subst i'; subst j'; subst x; subst y
      rfl

private theorem scatter_alias (l : List Position) (H : Heap) (dst : Position → ℕ)
    (val : Position → Heap → ℤ) (source : ℕ → Prop)
    (apart : ∀ a ∈ l, ¬source (dst a))
    (reads : ∀ a ∈ l, ∀ x y : Heap, (∀ z, source z → x z=y z) → val a x=val a y)
    (agree : ∀ a ∈ l, ∀ b ∈ l, dst a=dst b → ∀ h, val a h=val b h) :
    let result := l.foldl (fun cur a => scatter dst val a cur) H
    (∀ a ∈ l, result (dst a)=val a H) ∧
    ∀ z, (∀ a ∈ l, z≠dst a) → result z=H z := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih =>
    have mem (b : Position) (hb : b∈l) : b∈a::l := List.mem_cons_of_mem _ hb
    let H' := scatter dst val a H
    have init (z : ℕ) (hz : source z) : H' z=H z := by
      apply if_neg
      intro he; exact apart a (by simp) (he ▸ hz)
    obtain ⟨hit,miss⟩ := ih H' (fun b hb => apart b (mem b hb))
      (fun b hb => reads b (mem b hb)) (fun b hb c hc => agree b (mem b hb) c (mem c hc))
    dsimp only
    constructor
    · intro b hb
      rcases List.mem_cons.mp hb with eq|rest
      · subst b
        by_cases ex : ∃ c∈l, dst a=dst c
        · obtain ⟨c,hc,e⟩ := ex
          rw [e]; exact (hit c hc).trans ((reads c (mem _ hc) _ _ init).trans (agree a (by simp) c (mem _ hc) e H).symm)
        · exact (miss _ (fun c hc e => ex ⟨c,hc,e⟩)).trans (by simp [H',scatter])
      · exact (hit b rest).trans (reads b (mem b rest) _ _ init)
    · intro z avoid
      exact (miss _ (fun b hb => avoid b (mem _ hb))).trans (if_neg (avoid a (by simp)))

theorem grid_result (sh : ℕ → Shape) (j D n₀ N : ℕ) (H : Heap) :
    let result := gridFold (fun a u v => setCell (sh a) n₀ N D u v) j D H
    (∀ a<j, ∀ u<D, ∀ v<D, result (address (sh a) n₀ N D u v)=datum H (sh a) n₀ N u v) ∧
    ∀ z, z<target n₀ N ∨ target n₀ N+space D≤z → result z=H z := by
  let d (p : Position) := address (sh p.1) n₀ N D p.2.1 p.2.2
  let f (p : Position) (h : Heap) := datum h (sh p.1) n₀ N p.2.1 p.2.2
  have h := scatter_alias (points j D) H d f (fun z => z<target n₀ N)
    (by intro p _; simp [d,address])
    (by
      intro p hp h₁ h₂ eqn
      dsimp [f,datum]; split
      · rename_i test; apply eqn
        have lim : offset (sh p.1) N p.2.1 p.2.2<space N := by
          rcases test with ⟨row,col⟩
          cases es : sh p.1 with
          | unary i => exact offset_lt (.unary i) (y:=0) row (by omega)
          | cross i j => rw [es] at col; exact offset_lt (.cross i j) row col
        unfold target; omega
      · rfl)
    (by
      intro p hp q hq eqn h
      have u := (points_mem j D p).mp hp
      have v := (points_mem j D q).mp hq
      apply data_agree _ _ h u.2.1 u.2.2 v.2.1 v.2.2
      exact Nat.add_left_cancel eqn)
  dsimp only
  rw [gridFold_list]
  constructor
  · intro a ha u hu v hv
    exact h.1 (a,u,v) ((points_mem ..).mpr ⟨ha,hu,hv⟩)
  · intro z hz
    apply h.2 z
    intro p hp
    have e := (points_mem ..).mp hp
    have cut := offset_lt (sh p.1) e.2.1 e.2.2
    dsimp [d,address]; omega

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicRoot -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured Butterfly SquareCode SquareCode.Layout

def rootHeaders : List Atom := [
  .sub (-16) (-3) (-3), .add 0 (-16) (-3), .add 8 (-16) (-512), .add 320 (-16) (-12),
  .mul 321 (-2) (-2), .one (-16), .add 321 321 (-16)]

def bindRoot : Command := .seq (dst.code (-512)) (line rootHeaders)
def bindCost := dst.steps+7

structure Headers (n₀ N D L : ℕ) (out : Memory) : Prop where
  dimension : out 0=D
  weights : out (NativeFrame.reg 0 .weights)=(target n₀ N:ℤ)
  depth : out 320=L
  output : out 321=(origin n₀:ℤ)

theorem bind_runs {W n₀ N D L : ℕ} (m : Memory) (hd : m (-3)=D) (hn : m (-1)=N)
    (hg : m (-2)=n₀) (hl : m (-12)=L) :
    ∃ out, Runs W bindRoot m bindCost out ∧ Headers n₀ N D L out ∧
      ∀ z : ℕ, 321<z → out z=m z := by
  have sf : dst.safe (-512) W m := by simp [dst,src,words,n,Expr.safe]
  obtain ⟨a,act,av,af⟩ := dst.run m _ sf
  have v : a (-512)=(target n₀ N:ℤ) := by
    rw [av]; simp [dst,src,words,n,Expr.val,hn,hg,target,space,origin]
  let o := rootHeaders.foldl effect a
  have run : Runs W (line rootHeaders) a 7 o := line_runs _ _ (by simp [rootHeaders,safeLine,safe])
  have d := (af (-3) (by decide)).trans hd
  have g := (af (-2) (by decide)).trans hg
  have l := (af (-12) (by decide)).trans hl
  refine ⟨o,act.seq run,⟨?_,?_,?_,?_⟩,?_⟩
  · simp [o,rootHeaders,effect,update,d]
  · simp [o,rootHeaders,effect,update,NativeFrame.reg,NativeFrame.Field.offset,v]
  · simp [o,rootHeaders,effect,update,l]
  · simp [o,rootHeaders,effect,update,origin,g]; ring
  · intro z hz
    simp only [o,rootHeaders,List.foldl_cons,List.foldl_nil,effect,update]
    repeat' rw [if_neg (by omega)]
    exact af _ (by omega)

def saveOrder := line [.sub (-2) (-1) (-1),.add (-2) (-2) 0]

theorem save_runs (W : ℕ) (m : Memory) :
    ∃ o, Runs W saveOrder m 2 o ∧ o (-2)=m 0 ∧ ∀ z : ℤ, z≠ -2 → o z=m z := by
  let ops : List Atom := [.sub (-2) (-1) (-1),.add (-2) (-2) 0]
  refine ⟨ops.foldl effect m,line_runs _ _ (by simp [ops,safeLine,safe]),?_,?_⟩
  · simp [ops,effect,update]
  · intro z hz; simp [ops,effect,update,hz]

def prepareRoot (t : ℕ) (sh : ℕ → Shape) (j : ℕ) : Command :=
  .seq (Dyadic.sizeProgram t) (.seq saveOrder (.seq (blocks sh j) bindRoot))

def coefficient (sh : ℕ → Shape) : ℕ → ℕ
  | 0 => 0
  | i+1 => coefficient sh i+(writeBudget (sh i)+10)

theorem cost_le (sh : ℕ → Shape) (j : ℕ) {D : ℕ} (hd : 1≤D) :
    blockCost sh D j ≤ coefficient sh j*D^2 := by
  induction j with
  | zero => simp [blockCost,coefficient]
  | succ j ih =>
    have one : 1≤D^2 := Nat.one_le_pow _ _ hd
    have sq : D≤D^2 := by simpa [sq] using Nat.mul_le_mul_left D hd
    have each : gridCost (sh j) D≤(writeBudget (sh j)+10)*D^2 := by
      unfold gridCost; nlinarith only [one,sq]
    simpa only [blockCost,coefficient,Nat.add_mul] using Nat.add_le_add ih each

theorem root_runs {W n₀ t : ℕ} (sh : ℕ → Shape) (j : ℕ) (m : Memory)
    (hn : 32≤n₀) (order : m 0=n₀)
    (room : Division.Room W (roomNeeded n₀ (n₀^t) (2^(Nat.clog 2 (n₀^t))))) :
    let N := n₀^t
    let L := Nat.clog 2 N
    let D := 2^L
    ∃ T≤t+9+4*L+coefficient sh j*D^2+bindCost, ∃ out,
      Runs W (prepareRoot t sh j) m T out ∧ Headers n₀ N D L out ∧
      (∀ a<j, ∀ u<D, ∀ v<D, out (address (sh a) n₀ N D u v:ℕ)=datum (heap m) (sh a) n₀ N u v) ∧
      ∀ z : ℕ, target n₀ N+space D≤z → out z=m z := by
  let N := n₀^t
  let L := Nat.clog 2 N
  let D := 2^L
  have nd : N≤D := Nat.le_pow_clog (by decide) _
  have hd : 0<D := Nat.pow_pos (by decide)
  have small : Division.Room W (2*N) := lt_of_le_of_lt (Nat.cast_le.mpr (by change 2*N≤roomNeeded n₀ N D; unfold roomNeeded; omega)) room
  obtain ⟨p,start,fr,hN,hD,hL⟩ := Dyadic.size_runs W n₀ t (by omega) m order small
  obtain ⟨a,save,ag,af⟩ := save_runs W p
  have hN' := (af _ (by decide : (-1:ℤ)≠ -2)).trans hN
  have hD' := (af _ (by decide : (-3:ℤ)≠ -2)).trans hD
  have hg' : a (-2)=n₀ := ag.trans ((fr 0).trans order)
  obtain ⟨S,ts,b,run,dat,regs⟩ := blocks_run sh a hN' hD' hg' hd nd room j
  obtain ⟨out,bind,hdr,top⟩ := bind_runs (W:=W) b
    ((regs _ (by decide) (by decide)).trans hD') ((regs _ (by decide) (by decide)).trans hN')
    ((regs _ (by decide) (by decide)).trans hg') ((regs _ (by decide) (by decide)).trans ((af _ (by decide)).trans hL))
  have before : heap a=heap m := by
    funext z; exact (af _ (by omega)).trans (fr z)
  rw [before] at dat
  have result := grid_result sh j D n₀ N (heap m)
  have far : 321<target n₀ N := by
    have h := Nat.mul_le_mul hn hn
    unfold target origin; omega
  have tbound : S≤coefficient sh j*D^2 := ts.trans (cost_le sh j hd)
  refine ⟨_,by change t+7+4*L+(2+(S+bindCost))≤t+9+4*L+coefficient sh j*D^2+bindCost; omega,out,
    start.seq (save.seq (run.seq bind)),hdr,?_,?_⟩
  · intro i hi u hu v hv
    exact (top (address (sh i) n₀ N D u v) (far.trans_le (Nat.le_add_right _ _))).trans
      ((congrFun dat _).trans (result.1 i hi u hu v hv))
  · intro z hz
    rw [top z (far.trans_le ((Nat.le_add_right _ _).trans hz))]
    exact (congrFun dat _).trans (result.2 z (Or.inr hz))

def returnRoot : Command := .atom (.store 321 (NativeFrame.reg 0 .value))

theorem return_runs {W n₀ : ℕ} (m : Memory) (p : m 321=(origin n₀:ℤ))
    (fits : Fits W (origin n₀:ℤ)) :
    ∃ out, Runs W returnRoot m 1 out ∧ out (origin n₀:ℤ)=m (NativeFrame.reg 0 .value) ∧
      ∀ a, a≠(origin n₀:ℤ) → out a=m a := by
  refine ⟨_,Runs.atom (Step.store m 321 _ (p ▸ fits)),?_,?_⟩
  · simp [update,p]
  · intro a ha; simp [update,p,ha]

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicBound -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph

theorem dyadic_le {N : ℕ} (hn : 1≤N) : 2^Nat.clog 2 N≤2*N := by
  cases e : Nat.clog 2 N with
  | zero => simp; omega
  | succ l =>
    have lt : 2^l<N := Nat.pow_lt_of_lt_clog (by omega : l<Nat.clog 2 N)
    rw [pow_succ]; omega

theorem capacity {n₀ N D t : ℕ} (hn : 32≤n₀) (hN : N=n₀^t) (hd : D≤2*N) :
    roomNeeded n₀ N D ≤ n₀^(2*t+4) := by
  let A := n₀^(2*t+2)
  have one : 1≤n₀ := by omega
  have h₁ : 1≤A := Nat.one_le_pow _ _ one
  have h₂ : n₀*n₀≤A := by rw [←sq]; exact Nat.pow_le_pow_right one (by omega)
  have hn' : N≤A := by rw [hN]; exact Nat.pow_le_pow_right one (by omega)
  have hns : N*N≤A := by rw [hN,←pow_add]; exact Nat.pow_le_pow_right one (by omega)
  have hds : D*D≤4*(N*N) := by nlinarith only [Nat.mul_le_mul hd hd]
  have four : 440≤n₀^2 := by nlinarith only [Nat.mul_le_mul hn hn]
  calc
    _ ≤ 440*A := by unfold roomNeeded target space origin; omega
    _ ≤ n₀^2*A := Nat.mul_le_mul_right _ four
    _ = n₀^(2*t+4) := by unfold A; rw [←pow_add]; congr 1; omega

def rootRate (sh : ℕ → Shape) (j t : ℕ) := t+13+4*coefficient sh j+bindCost

theorem time_quadratic (sh : ℕ → Shape) (j t : ℕ) {N : ℕ} (hn : 1≤N) :
    t+9+4*Nat.clog 2 N+coefficient sh j*(2^Nat.clog 2 N)^2+bindCost ≤
      rootRate sh j t*N^2 := by
  let L := Nat.clog 2 N
  let D := 2^L
  have dc : D≤2*N := dyadic_le hn
  have ds : D^2≤4*N^2 := by nlinarith only [Nat.mul_le_mul dc dc]
  have dp := Nat.mul_le_mul_left (coefficient sh j) ds
  have ls : L≤N := Nat.clog_le_of_le_pow N.lt_two_pow_self.le
  have ns : N≤N^2 := by simpa [sq] using Nat.mul_le_mul_left N hn
  have a := Nat.mul_le_mul_left (t+9+bindCost) (show 1≤N^2 by omega)
  change t+9+4*L+coefficient sh j*D^2+bindCost ≤ _
  unfold rootRate; nlinarith only [a,ls,ns,dp]

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicTable -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured SquareCode.Layout WeightedProof

def table (t : ℕ) := prepareRoot t Table.shapeAt 90
def tableRate (t : ℕ) := rootRate Table.shapeAt 90 t

theorem table_runs {W n₀ t : ℕ} (m : Memory) (hn : 32≤n₀) (order : m 0=n₀)
    (room : Division.Room W (roomNeeded n₀ (n₀^t) (2^(Nat.clog 2 (n₀^t)))))
    (w : WeightKey (n₀^t) → ℚ)
    (old : ∀ a : WeightKey (n₀^t), (m (origin n₀+Table.wordIndex a:ℕ):ℚ)=w a) :
    let N := n₀^t
    let L := Nat.clog 2 N
    let D := 2^L
    ∃ T≤tableRate t*N^2, ∃ out, Runs W (table t) m T out ∧ Headers n₀ N D L out ∧
      (∀ a : WeightKey D, (out (target n₀ N+Table.wordIndex a:ℕ):ℚ)=literal w (padTag a)) ∧
      ∀ z : ℕ, target n₀ N+space D≤z → out z=m z := by
  let N := n₀^t
  let D := 2^Nat.clog 2 N
  have hN : 1≤N := Nat.one_le_pow _ _ (by omega)
  have hd : 0<D := Nat.pow_pos (by decide)
  obtain ⟨T,ht,out,run,headers,all,fr⟩ := root_runs Table.shapeAt 90 m hn order room
  refine ⟨T,ht.trans (time_quadratic _ 90 t hN),out,run,headers,?_,fr⟩
  rintro (⟨i,x⟩|⟨i,j,x,y⟩)
  · have p := all i.val (by have := i.isLt; omega) x.val x.isLt 0 hd
    rw [Table.unaryAt] at p
    change out (target n₀ N+Table.wordIndex (.inl (i,x)):ℕ)=_ at p
    rw [p]; by_cases hx : x.val<n₀^t
    · simpa [datum,colOK,hx,offset,heap,literal,padTag,Table.wordIndex] using old (.inl (i,⟨x,hx⟩))
    · simp [datum,colOK,hx,literal,padTag]
  · let q := 9+i.val*9+j.val
    have hp : q<90 := by have := i.isLt; have := j.isLt; dsimp [q]; omega
    have p := all q hp x.val x.isLt y.val y.isLt
    rw [show Table.shapeAt q=.cross i j from Table.crossAt i j] at p
    change out (target n₀ N+Table.wordIndex (.inr (i,j,x,y)):ℕ)=_ at p
    rw [p]; by_cases hxy : x.val<n₀^t ∧ y.val<n₀^t
    · simpa [datum,colOK,hxy,offset,heap,literal,padTag,Table.wordIndex]
        using old (.inr (i,j,⟨x,hxy.1⟩,⟨y,hxy.2⟩))
    · simp [datum,colOK,hxy,literal,padTag]

end VWZClique.IntegerRAM.DyadicCell
end

/- WordGraphPost -/
section
namespace VWZClique.IntegerRAM
open Structured

theorem fits_widen {W V : ℕ} (hW : W≤V) {z : ℤ} (hz : Fits W z) : Fits V z := by
  have h : (2:ℤ)^(W-1)≤2^(V-1) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hW 1)
  exact ⟨(neg_le_neg h).trans hz.1,hz.2.trans_le h⟩

theorem step_widen {W V : ℕ} (hW : W≤V) {c m out} (h : Step W c m out) : Step V c m out := by
  cases h with
  | one => exact .one ..
  | add => exact .add ..
  | sub => exact .sub ..
  | mul => exact .mul ..
  | load m d p hf => exact .load m d p (fits_widen hW hf)
  | store m p s hf => exact .store m p s (fits_widen hW hf)

theorem runs_widen {W V : ℕ} (hW : W≤V) {c m T out} (h : Runs W c m T out) :
    Runs V c m T out := by
  induction h with
  | skip => exact .skip _
  | atom s => exact .atom (step_widen hW s)
  | seq _ _ ha hb => exact .seq ha hb
  | guard_skip hf hn => exact .guard_skip (fits_widen hW hf) hn
  | guard_take hf hn _ more => exact .guard_take (fits_widen hW hf) hn more
  | loop_done _ hf hn body => exact .loop_done body (fits_widen hW hf) hn
  | loop_again _ hf hn _ body more => exact .loop_again body (fits_widen hW hf) hn more

end VWZClique.IntegerRAM

namespace VWZClique.IntegerRAM.Graph.Table
open Structured BlockReduction

/-- Entry contract for an evaluator of the grouped instance. Its arguments
are the native input-order word and all the populated unary and edge weights. -/
structure Ready {n : ℕ} (t k : ℕ) (G : SimpleGraph (Fin n)) (hn : 1≤n) (m : Memory) : Prop where
  order : m 0=n
  values : ∀ a : WeightKey (n^t), (m (((MonDepMW.graphInput G).length+wordIndex a:ℕ):ℤ) : ℚ)=
    weights G k ⟨0,hn⟩ a

end VWZClique.IntegerRAM.Graph.Table
end

/- CliqueIntegerPlan -/
section
/-! Apply the integer recursion to the original graph at every input size. -/

namespace VWZClique.BlockReduction
open UniformFolds WeightedProof OAI.MatrixMultiplication.Arithmetic

theorem graphWeights_binary {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (k : ℕ)
    (i : WeightKey (2^graphLength n k)) : Binary (graphWeights G hn k i) := by
  let w := weights (F := ℚ) (t := (k+8)/9) G k ⟨0,hn⟩
  have h (x : WeightKey (n^((k+8)/9))) : Binary (w x) := weights_binary G k _ x
  have zero : Binary (0:ℚ) := Or.inl rfl
  cases i with
  | inl a =>
    obtain ⟨u,x⟩ := a
    change Binary (literal w (padTag (.inl (u,x))))
    by_cases hx : x.val < n^((k+8)/9) <;> simp [padTag,hx,literal,h,zero]
  | inr a =>
    obtain ⟨u,v,x,y⟩ := a
    change Binary (literal w (padTag (.inr (u,v,x,y))))
    by_cases hx : x.val < n^((k+8)/9) ∧ y.val < n^((k+8)/9) <;> simp [padTag,hx,literal,h,zero]

theorem graph_integer_exact {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (k : ℕ) :
    integerPlan (graphLength n k) (fixed ⊤) (graphWeights G hn k) = (count G k : ℤ) := by
  have bound := Nat.le_pow_clog (by decide : 1 < 2) (n^((k+8)/9))
  have correct := integerPlan_correct _ ⊤ _ (graphWeights_binary G hn k)
  have pad := weights_padded bound (⊤ : SimpleGraph V)
    (weights (F := ℚ) (t := (k+8)/9) G k ⟨0,hn⟩)
  have result := correct.trans (pad.trans (weighted_eq_count_ceil hn G k))
  exact_mod_cast result

end VWZClique.BlockReduction
end

/- NativeDyadicGraph -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Structured Graph BlockReduction

/-- The prepared root has all binary, dyadically padded weights and both persistent
    headers required by the interpreter. For a fixed k the native program and
    width multiplier are independent of the order of the input graph. -/
theorem graph_runs {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (hn : 32≤n) (m : Memory)
    (ready : Table.Ready ((k+8)/9) k G (by omega) m) :
    let t := (k+8)/9
    let N := n^t
    let L := graphLength n k
    let D := 2^L
    ∃ T≤tableRate t*N^2, ∃ out,
      Runs ((2*t+6)*(n.log2+1)) (table t) m T out ∧ Headers n N D L out ∧
      (∀ a : WeightKey D, (out (target n N+Table.wordIndex a:ℕ):ℚ)=graphWeights G (by omega) k a) ∧
      ∀ z : ℕ, target n N+space D≤z → out z=m z := by
  let t := (k+8)/9
  let N := n^t
  have hN : 1≤N := Nat.one_le_pow _ _ (by omega)
  have cap := capacity (t:=t) hn (N:=N) rfl (dyadic_le hN)
  have wide : Division.Room ((2*t+6)*(n.log2+1)) (n^(2*t+4)) := Division.room_pow (by omega) (by omega)
  have room : Division.Room ((2*t+6)*(n.log2+1)) (roomNeeded n N (2^Nat.clog 2 N)) :=
    lt_of_le_of_lt (Nat.cast_le.mpr cap) wide
  exact table_runs m hn ready.order room (weights (F:=ℚ) (t:=t) G k ⟨0,by omega⟩) <| by
    intro a
    have e := ready.values a
    rw [graphInput_length] at e
    exact e

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeDyadicOriginal -/
section
namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured BlockReduction

def original (k : ℕ) :=
  let t := (k+8)/9
  Command.seq (Table.machine t k) (table t)

theorem original_runs {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (hn : 32≤n) :
    let t := (k+8)/9
    let N := n^t
    let L := graphLength n k
    let D := 2^L
    ∃ T≤(Table.coefficient t+tableRate t)*N^3, ∃ out,
      Runs ((2*t+11)*(n.log2+1)) (original k) (input (MonDepMW.graphInput G)) T out ∧
      Headers n N D L out ∧
      ∀ a : WeightKey D, (out (target n N+Table.wordIndex a:ℕ):ℚ)=graphWeights G (by omega) k a := by
  let t := (k+8)/9
  let N := n^t
  have hN : 1≤N := Nat.one_le_pow _ _ (by omega)
  obtain ⟨T,preTime,m,pre,values,preserved⟩ := Table.preprocess_runs (by omega) G t k
  have g := graphAt_input G
  have hlen : 0<(MonDepMW.graphInput G).length := by rw [graphInput_length]; omega
  have ready : Table.Ready t k G (by omega) m := ⟨(preserved 0 hlen).trans g.1,values⟩
  obtain ⟨S,postTime,o,post,header,output,_⟩ := graph_runs G k hn m ready
  have p : N^2≤N^3 := Nat.pow_le_pow_right hN (by decide)
  refine ⟨_,?_,o,pre.seq (runs_widen (Nat.mul_le_mul_right _ (by omega)) post),header,output⟩
  change T+S≤(Table.coefficient t+tableRate t)*N^3
  have hT : T≤Table.coefficient t*N^3 := (Nat.le_succ _).trans preTime
  have hS : S≤tableRate t*N^3 := postTime.trans (Nat.mul_le_mul_left _ p)
  rw [Nat.add_mul]; exact Nat.add_le_add hT hS

theorem graph_return {n k b : ℕ} (G : SimpleGraph (Fin n)) (hn : 2≤n) (hb : 6≤b)
    (m : Memory) (ptr : m 321=(origin n:ℤ)) (value : m (NativeFrame.reg 0 .value)=(count G k:ℤ)) :
    ∃ out, Runs (b*(n.log2+1)) returnRoot m 1 out ∧
      out ((MonDepMW.graphInput G).length:ℤ)=(count G k:ℤ) := by
  have wide : Division.Room (b*(n.log2+1)) (n^4) := Division.room_pow (by omega) hb
  have two : 2≤n*n := (by decide : 2≤2*2).trans (Nat.mul_le_mul hn hn)
  have upper : origin n≤n^4 := by
    unfold origin; nlinarith only [Nat.mul_le_mul two (Nat.le_refl (n*n)),two]
  have fits : Fits (b*(n.log2+1)) (origin n:ℤ) := by apply wide.fits <;> omega
  obtain ⟨o,run,read,_⟩ := return_runs m ptr fits
  exact ⟨o,run,by rw [graphInput_length]; exact read.trans value⟩

end VWZClique.IntegerRAM.DyadicCell
end

/- NativeGraphProgram -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal BlockReduction Graph WeightedProof

noncomputable def graphProgram (k : ℕ)
    (proj : ℕ → SimpleGraph V → Equiv.Perm V → Command)
    (push : ℕ → SimpleGraph V → Equiv.Perm V → Branch → Command) : Command :=
  .seq (DyadicCell.original k) <| .seq (emitPlan (ops leafOp proj push) (fixed ⊤) 0) DyadicCell.returnRoot

/-- Connect the recursion to the published graph input and output cells.
The hypotheses concern only the two per-node kernels and their working storage. -/
theorem graph_program_runs {n k b : ℕ} (G : SimpleGraph (Fin n)) (hn : 32≤n)
    {lay : StackLayout} {proj push P B}
    (endsAt : lay.outputAddress=DyadicCell.origin n)
    (startsAt : lay.base 0=DyadicCell.target n (n^((k+8)/9)))
    (wide : 2*((k+8)/9)+11≤b)
    (localRuns : @Kernels (graphLength n k) (b*(n.log2+1)) lay proj push P B)
    (mem : ∀ d≤36, Division.Room (b*(n.log2+1))
      (lay.base d+9*2^graphLength n k+81*(2^graphLength n k*2^graphLength n k)))
    (six : Division.Room (b*(n.log2+1)) ((2^graphLength n k)^6)) :
    let t := (k+8)/9
    let N := n^t
    let L := graphLength n k
    ∃ f ≤ (Table.coefficient t+DyadicCell.tableRate t)*N^3 + (cost L (fees L P B) (fixed ⊤)+1),
      ∃ out, Runs (b*(n.log2+1)) (graphProgram k proj push) (input (MonDepMW.graphInput G)) f out ∧
        out ((MonDepMW.graphInput G).length:ℤ) = integerPlan L (fixed ⊤) (graphWeights G (by omega) k) := by
  let t := (k+8)/9
  let N := n^t
  let L := graphLength n k
  let W := b*(n.log2+1)
  obtain ⟨f,hf,y,setup,headers,weights⟩ := DyadicCell.original_runs G k hn
  let w := graphWeights G (by omega : 0<n) k
  have rep : @Repr L lay [.input 0 w] y := by
    exact ⟨⟨headers.dimension,headers.depth,endsAt ▸ headers.output⟩,
      ⟨startsAt ▸ headers.weights,startsAt ▸ weights⟩,trivial⟩
  obtain ⟨s,hs,z,recurs,endState⟩ := execute_from_two localRuns mem six (fixed ⊤) 0
    (by simpa using edge_limit (⊤ : SimpleGraph V)) w (graphWeights_binary G (by omega) k) [] y rep
  have addr : z 321 = (DyadicCell.origin n:ℤ) := endsAt ▸ endState.1.output
  have semantic := graph_integer_exact G (by omega : 0<n) k
  have val : z (reg 0 .value)=integerPlan L (fixed ⊤) w := endState.2.1
  obtain ⟨last,ret,result⟩ := DyadicCell.graph_return (b:=b) G (by omega) (by omega) z addr (val.trans semantic)
  exact ⟨_,Nat.add_le_add hf (Nat.add_le_add_right hs 1),last,
    .seq (runs_widen (Nat.mul_le_mul_right _ wide) setup) (.seq recurs ret),result.trans semantic.symm⟩

end VWZClique.IntegerRAM.NativeFrame
end

/- NativeAssemblyRate -/
section
namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal BlockReduction Graph WeightedProof

theorem verifiedPublicationStep {mm : ℕ→ℕ} {T U A : ℕ} (impl : Implemented mm T U A) :
    Realizes mm T U A := by
  refine ⟨32,?_⟩
  intro k hk
  obtain ⟨b,hb,wide,localK⟩ := impl.kernels k hk
  let t := (k+8)/9
  let C := Table.coefficient t+DyadicCell.tableRate t+1+37*impl.factor
  have pos : 0<C := by dsimp [C]; omega
  refine ⟨graphProgram k impl.projection impl.push,b,impl.logPower,(C:ℝ),hb,by exact_mod_cast pos,?_⟩
  intro n G hn large
  let L := graphLength n k
  let N := n^t
  let D := 2^L
  let p := fixed (⊤ : SimpleGraph V)
  let work := planWork mm T U A L p
  let logs := (L+1)^impl.logPower
  let K := impl.factor*logs
  let fee := fees L (impl.projectTime L) (impl.pushTime L)
  obtain ⟨ker,space,six⟩ := localK n large
  obtain ⟨f,ht,out,run,ans⟩ := graph_program_runs G large (lay:=NativeArena.forGraph n k large)
    rfl rfl wide ker space six
  refine ⟨f,out,?_,run,ans⟩
  have hcost := cost_le mm T U A L K fee (impl.sparseTime L)
    (fun H => by simpa [fee,fees] using impl.projectedTime L H)
    (fun H => by have u := impl.pushBound L H; change impl.pushTime L H + 5 + 1 ≤ K * (U * (2^L)^5); exact u) p
  have e := edge_limit (⊤ : SimpleGraph V)
  have hnear : cost L fee p≤37*K*work :=
    hcost.trans (Nat.mul_le_mul_right work (Nat.mul_le_mul_right K (by omega)))
  have flo := work_floor mm T U A L p
  have lo : D^5≤work := (Nat.le_mul_of_pos_left _ impl.positive).trans flo
  have domain : N≤D := Nat.le_pow_clog (by decide) _
  have dpos : 1 ≤ D := Nat.one_le_pow _ _ (by decide)
  have powBound (a : ℕ) (ha : a≤5) : N^a≤work :=
    ((Nat.pow_le_pow_left domain a).trans (Nat.pow_le_pow_right dpos ha)).trans lo
  have lpos : 1 ≤ logs := Nat.one_le_pow _ _ (by omega)
  have wt : work≤logs*work := Nat.le_mul_of_pos_left _ lpos
  have wpos : 1≤work := by have v : 1≤D^5 := Nat.one_le_pow _ _ dpos; omega
  have charge : f≤ C*logs*work := by
    have full := Nat.add_le_add (Nat.mul_le_mul_left (Table.coefficient t+DyadicCell.tableRate t) ((powBound 3 (by decide)).trans wt))
      (Nat.add_le_add hnear (wpos.trans wt))
    apply ht.trans
    calc
      _ ≤ _ := full
      _ = _ := by dsimp [C,K]; ring
  exact_mod_cast charge

end VWZClique.IntegerRAM.NativeFrame
end


theorem solution {mm : ℕ → ℕ} {T U A : ℕ}
    (impl : VWZClique.IntegerRAM.NativeFrame.Implemented mm T U A) :
    VWZClique.NativeTraversal.Realizes mm T U A
  := VWZClique.IntegerRAM.NativeFrame.verifiedPublicationStep impl
